use crate::server::{AcornLanguageServer, LspClient, ServerArgs};
use assert_fs::fixture::ChildPath;
use assert_fs::prelude::*;
use assert_fs::TempDir;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use tower_lsp::lsp_types::{
    Diagnostic, DidChangeTextDocumentParams, DidOpenTextDocumentParams, DidSaveTextDocumentParams,
    TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentItem, Url,
    VersionedTextDocumentIdentifier,
};
use tower_lsp::LanguageServer;

/// Mock implementation of LspClient for testing
#[derive(Clone)]
struct MockClient {
    // Store diagnostics by URL
    diagnostics: Arc<RwLock<HashMap<Url, Vec<Diagnostic>>>>,
}

impl MockClient {
    fn new() -> Self {
        MockClient {
            diagnostics: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Wait for diagnostics to be published for a given URL
    /// Returns the diagnostics if they arrive within the timeout
    async fn wait_for_diagnostics(&self, url: &Url, timeout_secs: u64) -> Option<Vec<Diagnostic>> {
        let deadline = tokio::time::Instant::now() + Duration::from_secs(timeout_secs);

        while tokio::time::Instant::now() < deadline {
            {
                let diags = self.diagnostics.read().await;
                if let Some(diagnostics) = diags.get(url) {
                    if !diagnostics.is_empty() || diags.contains_key(url) {
                        // Return if we have diagnostics or an explicit empty list
                        return Some(diagnostics.clone());
                    }
                }
            }
            // Check every 10ms
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
        None
    }
}

#[async_trait::async_trait]
impl LspClient for MockClient {
    async fn publish_diagnostics(
        &self,
        uri: Url,
        diagnostics: Vec<Diagnostic>,
        _version: Option<i32>,
    ) {
        let mut diags = self.diagnostics.write().await;
        diags.insert(uri, diagnostics);
    }
}

/// Test fixture that sets up an Acorn language server with a temp directory.
/// Automatically cleans up when dropped.
struct TestFixture {
    _temp_dir: TempDir, // Must keep this alive or the directory gets deleted!
    pub src_dir: ChildPath,
    pub build_dir: ChildPath,
    pub client: Arc<MockClient>,
    pub server: AcornLanguageServer,
}

impl TestFixture {
    /// Creates a new test fixture with standard Acorn project layout
    fn new() -> Self {
        // Create temp directory structure
        let temp_dir = TempDir::new().unwrap();
        temp_dir.child("acorn.toml").write_str("").unwrap();
        let src_dir = temp_dir.child("src");
        src_dir.create_dir_all().unwrap();
        let build_dir = temp_dir.child("build");
        build_dir.create_dir_all().unwrap();

        // This is the "developing acornlib" setup
        let args = ServerArgs {
            workspace_root: Some(temp_dir.path().to_str().unwrap().to_string()),
            extension_root: String::new(),
        };

        let client = Arc::new(MockClient::new());
        let server = AcornLanguageServer::new(client.clone(), &args);

        TestFixture {
            _temp_dir: temp_dir,
            src_dir,
            build_dir,
            client,
            server,
        }
    }

    /// Converts a relative path to a file:// URL that can be used with set_full_text
    fn url(&self, path: &str) -> Url {
        let full_path = self.src_dir.path().join(path);
        Url::from_file_path(full_path).unwrap()
    }

    /// Open a document with the given content
    async fn open(&self, filename: &str, content: &str, version: i32) {
        self.server
            .did_open(DidOpenTextDocumentParams {
                text_document: TextDocumentItem {
                    uri: self.url(filename),
                    language_id: "acorn".to_string(),
                    version,
                    text: content.to_string(),
                },
            })
            .await;
    }

    /// Change a document's content (replaces entire content)
    async fn change(&self, filename: &str, content: &str, version: i32) {
        self.server
            .did_change(DidChangeTextDocumentParams {
                text_document: VersionedTextDocumentIdentifier {
                    uri: self.url(filename),
                    version,
                },
                content_changes: vec![TextDocumentContentChangeEvent {
                    range: None,
                    range_length: None,
                    text: content.to_string(),
                }],
            })
            .await;
    }

    /// Save a document with the given content
    async fn save(&self, filename: &str, content: &str) {
        self.server
            .did_save(DidSaveTextDocumentParams {
                text_document: TextDocumentIdentifier {
                    uri: self.url(filename),
                },
                text: Some(content.to_string()),
            })
            .await;
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_server_basic() {
    let fx = TestFixture::new();

    let text1 = "theorem foo { true }";
    let text2 = "theorem bar { true }";

    fx.open("foo.ac", text1, 1).await;
    fx.change("foo.ac", text2, 2).await;
    fx.save("foo.ac", text2).await;

    // Wait for diagnostics to verify the build happened
    let url = fx.url("foo.ac");
    let diagnostics = fx.client.wait_for_diagnostics(&url, 5).await;
    assert!(
        diagnostics.is_some(),
        "Expected to receive diagnostics from build"
    );

    // The build should complete with no errors for this simple valid theorem
    let diags = diagnostics.unwrap();
    assert!(
        diags.is_empty(),
        "Expected no diagnostic errors, got: {:?}",
        diags
    );

    // Give the build a bit more time to write cache files
    tokio::time::sleep(Duration::from_millis(100)).await;

    // Check that a cache was created
    assert!(fx.build_dir.child("foo.yaml").exists());
}
