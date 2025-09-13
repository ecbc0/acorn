use std::sync::Arc;

use dashmap::DashMap;
use tokio::sync::RwLock;
use tokio_util::sync::CancellationToken;
use tower_lsp::jsonrpc;
use tower_lsp::lsp_types::*;

use crate::block::NodeCursor;
use crate::interfaces::{InfoParams, InfoResponse, SearchParams, SearchResponse, SearchStatus};
use crate::module::{LoadState, ModuleDescriptor};
use crate::processor::Processor;
use crate::project::Project;
use crate::prover::{Outcome, ProverParams};

use super::live_document::LiveDocument;
use super::{log, to_path};

// A search job is a long-running job that searches for a proof.
// The language server can work on one search job at a time.
// The SearchJob tracks information around that request.
// It is clonable so that it can be used both by the thread doing the task, and
// threads handling requests.
// The thread doing the search updates the task with its information, while threads handling
// concurrent user requests can read it.
#[derive(Clone)]
pub struct SearchJob {
    project: Arc<RwLock<Project>>,
    url: Url,
    version: i32,

    // While we are proving, most of the time the thread running the 'run' method
    // will hold a write lock on the processor.
    // The task will release and reacquire the lock intermittently, and the RwLock is fair so other
    // threads get a chance to use the processor.
    processor: Arc<RwLock<Processor>>,

    // The module that we're searching for a proof in
    descriptor: ModuleDescriptor,

    // The line in the document the user selected to kick off this task.
    selected_line: u32,

    // The path to the goal
    path: Vec<usize>,

    // A displayable name for the goal
    goal_name: String,

    // The range of the goal in the document
    goal_range: Range,

    // The Status is periodically updated by the task.
    // It can indicate either partial progress or completion.
    status: Arc<RwLock<SearchStatus>>,

    // Cancel this token when a subsequent search job has been created
    cancellation_token: CancellationToken,

    // Zero-based line where we would insert a proof for this goal
    proof_insertion_line: u32,

    // Whether we need to also insert a block, if we do insert a proof.
    insert_block: bool,

    // The search id set by the extenson for the original search that created this task.
    // The extension may send new searches with essentially the same parameters, that we
    // discard. This is inevitable because the extension doesn't have enough information to
    // disambiguate searches. Only the language server does.
    // Thus, when we get redundant searches, we keep using the original id downstream.
    id: i32,
}

impl SearchJob {
    // Makes a response based on the current state of the task
    async fn response(&self) -> SearchResponse {
        let status = self.status.read().await.clone();
        SearchResponse {
            uri: self.url.clone(),
            version: self.version,
            failure: None,
            loading: false,
            goal_name: Some(self.goal_name.clone()),
            goal_range: Some(self.goal_range.clone()),
            status,
            proof_insertion_line: self.proof_insertion_line,
            insert_block: self.insert_block,
            id: self.id,
        }
    }

    // Runs the search job.
    async fn run(&self) {
        // This holds a read lock on the project the whole time.
        // It seems like we should be able to avoid this, but maybe it's just fine.
        let project = self.project.read().await;
        let env = match project.get_env(&self.descriptor) {
            Some(env) => env,
            None => {
                log(&format!("no environment for {:?}", self.descriptor));
                return;
            }
        };

        log(&format!("running search job for {}", self.goal_name));

        loop {
            // Each iteration through the loop reacquires the write lock on the prover.
            // This lets other threads access the prover in between iterations.
            let processor = &mut *self.processor.write().await;
            let outcome = processor.search(ProverParams::PARTIAL);
            let status = match &outcome {
                Outcome::Success => {
                    let proof = processor.get_condensed_proof().unwrap();
                    let steps = processor.prover().to_proof_info(
                        &proof,
                        &project,
                        &env.bindings,
                        processor.normalizer(),
                    );

                    let (code, error) = match proof.to_code(&env.bindings) {
                        Ok(code) => (Some(code), None),
                        Err(e) => (None, Some(e.to_string())),
                    };

                    SearchStatus::success(
                        code,
                        error,
                        steps,
                        proof.needs_simplification(),
                        processor.prover(),
                    )
                }

                Outcome::Inconsistent | Outcome::Exhausted | Outcome::Constrained => {
                    SearchStatus::stopped(processor.prover(), &outcome)
                }

                Outcome::Timeout => SearchStatus::pending(processor.prover()),

                Outcome::Interrupted => {
                    // No point in providing a result for this task, since nobody is listening.
                    log(&format!("goal {} interrupted", self.goal_name));
                    return;
                }
            };

            // Update the status
            let mut locked_status = self.status.write().await;
            *locked_status = status;

            if outcome != Outcome::Timeout {
                // We're done
                log(&format!("search job for {} completed", self.goal_name));
                break;
            }
        }
    }
}

// Manages search jobs for the language server
pub struct SearchManager {
    // The current search job, if any
    current_job: RwLock<Option<SearchJob>>,
}

impl SearchManager {
    pub fn new() -> Self {
        SearchManager {
            current_job: RwLock::new(None),
        }
    }

    // Cancels any current search job and runs the new job, if it is not None.
    async fn set_search_job(&self, new_job: Option<SearchJob>) {
        // Replace the locked singleton job
        {
            let mut locked_job = self.current_job.write().await;
            if let Some(old_job) = locked_job.as_ref() {
                // Cancel the old job
                old_job.cancellation_token.cancel();
            }
            *locked_job = new_job.clone();
        }

        if let Some(new_job) = new_job {
            tokio::spawn(async move {
                new_job.run().await;
            });
        }
    }

    fn search_fail(&self, params: SearchParams, message: &str) -> jsonrpc::Result<SearchResponse> {
        log(message);
        Ok(SearchResponse {
            failure: Some(message.to_string()),
            ..SearchResponse::new(params)
        })
    }

    pub async fn handle_search_request(
        &self,
        params: SearchParams,
        project: &Arc<RwLock<Project>>,
        documents: &DashMap<Url, Arc<RwLock<LiveDocument>>>,
    ) -> jsonrpc::Result<SearchResponse> {
        match self
            .search_request_helper(params.clone(), project, documents)
            .await
        {
            Ok(response) => Ok(response),
            Err(message) => self.search_fail(params, &message),
        }
    }

    async fn search_request_helper(
        &self,
        params: SearchParams,
        project: &Arc<RwLock<Project>>,
        documents: &DashMap<Url, Arc<RwLock<LiveDocument>>>,
    ) -> Result<SearchResponse, String> {
        let doc = match documents.get(&params.uri) {
            Some(doc) => doc,
            None => {
                return Err("no text available".to_string());
            }
        };
        let doc = doc.read().await;

        // Check if this request matches our current task, based on the selected line.
        // This is less general than checking the full path, but we don't have the
        // full path until we acquire a lock on the project.
        if let Some(current_job) = self.current_job.read().await.as_ref() {
            if current_job.url == params.uri
                && current_job.version == params.version
                && current_job.selected_line == params.selected_line
            {
                return Ok(current_job.response().await);
            }
        }

        let project_guard = project.read().await;
        let path = match to_path(&params.uri) {
            Some(path) => path,
            None => {
                // There should be a path available, because we don't run this task without one.
                return Err("no path available in SearchJob::run".to_string());
            }
        };
        match project_guard.get_version(&path) {
            Some(project_version) => {
                if params.version < project_version {
                    let message = format!(
                        "user requested version {} but the project has version {}",
                        params.version, project_version
                    );
                    return Err(message);
                }
                if params.version > project_version {
                    // The requested version is not loaded yet.
                    return Ok(SearchResponse {
                        loading: true,
                        ..SearchResponse::new(params)
                    });
                }
            }
            None => {
                return Err(format!("the project has not opened {}", path.display()));
            }
        }
        let descriptor = match project_guard.descriptor_from_path(&path) {
            Ok(name) => name,
            Err(e) => {
                return Err(format!("descriptor_from_path failed: {:?}", e));
            }
        };
        let env = match project_guard.get_module(&descriptor) {
            LoadState::Ok(env) => env,
            _ => {
                return Err(format!("could not load module from {:?}", descriptor));
            }
        };

        let path = env.path_for_line(params.selected_line)?;

        // Check if this request matches our current task, based on the full path of the goal.
        // This is slower (because we had to acquire the project lock first)
        // but catches more situations than just checking the selected line.
        if let Some(current_job) = self.current_job.read().await.as_ref() {
            if current_job.url == params.uri
                && current_job.version == params.version
                && current_job.path == path
            {
                return Ok(current_job.response().await);
            }
        }
        let cursor = NodeCursor::from_path(env, &path);
        let goal = cursor.goal()?;
        let cancellation_token = CancellationToken::new();
        let mut processor = Processor::with_token(&project_guard, cancellation_token.clone());
        for fact in cursor.usable_facts(&project_guard) {
            processor.add_fact(fact)?;
        }
        processor.set_goal(&goal)?;
        let status = SearchStatus::pending(processor.prover());

        // Create a new search job
        let new_job = SearchJob {
            project: project.clone(),
            url: params.uri.clone(),
            version: doc.saved_version(),
            processor: Arc::new(RwLock::new(processor)),
            descriptor,
            selected_line: params.selected_line,
            path,
            goal_name: goal.name.clone(),
            goal_range: goal.proposition.source.range,
            status: Arc::new(RwLock::new(status)),
            cancellation_token,
            proof_insertion_line: goal.proof_insertion_line,
            insert_block: goal.insert_block,
            id: params.id,
        };

        // A minimal response before any data has been collected
        let mut response = new_job.response().await;
        response.loading = true;

        self.set_search_job(Some(new_job)).await;

        Ok(response)
    }

    fn info_fail(&self, params: InfoParams, message: &str) -> jsonrpc::Result<InfoResponse> {
        log(message);
        Ok(InfoResponse {
            search_id: params.search_id,
            failure: Some(message.to_string()),
            result: None,
        })
    }

    pub async fn handle_info_request(
        &self,
        params: InfoParams,
        project: &Arc<RwLock<Project>>,
    ) -> jsonrpc::Result<InfoResponse> {
        let locked_job = self.current_job.read().await;

        let job = match locked_job.as_ref() {
            Some(job) => job,
            None => return self.info_fail(params, "no search job available"),
        };
        if job.id != params.search_id {
            let failure = format!(
                "info request has search id {}, job has id {}",
                params.search_id, job.id
            );
            return self.info_fail(params, &failure);
        }
        let project_guard = project.read().await;
        let processor = &*job.processor.read().await;
        let env = match project_guard.get_env(&job.descriptor) {
            Some(env) => env,
            None => {
                return self.info_fail(params, "no environment available");
            }
        };
        let result = processor.prover().info_result(
            params.clause_id,
            &project_guard,
            &env.bindings,
            processor.normalizer(),
        );
        let failure = match result {
            Some(_) => None,
            None => Some(format!("no info available for clause {}", params.clause_id)),
        };
        Ok(InfoResponse {
            search_id: params.search_id,
            failure,
            result,
        })
    }
}