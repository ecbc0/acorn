use tokio::sync::{RwLock, RwLockReadGuard};
use tokio_util::sync::CancellationToken;

use crate::project::{Project, ProjectConfig};
use std::path::PathBuf;

/// Manages a Project with associated cancellation token for builds
pub struct ProjectManager {
    project: RwLock<Project>,
    cancel: RwLock<CancellationToken>,
}

/// A read-only view of the project with its associated cancellation token
pub struct ProjectView<'a> {
    pub guard: RwLockReadGuard<'a, Project>,
    pub cancel: CancellationToken,
}

impl ProjectManager {
    /// Creates a new ProjectManager with the given project configuration
    pub fn new(src_dir: PathBuf, build_dir: PathBuf, config: ProjectConfig) -> Self {
        let project = Project::new(src_dir, build_dir, config);
        ProjectManager {
            project: RwLock::new(project),
            cancel: RwLock::new(CancellationToken::new()),
        }
    }

    /// Gets a read-only view of the project
    pub async fn read(&self) -> ProjectView<'_> {
        let guard = self.project.read().await;
        let cancel = self.cancel.read().await.clone();
        ProjectView { guard, cancel }
    }

    /// Mutates the project with exclusive access
    /// Automatically cancels the old token and creates a new one after mutation
    pub async fn mutate<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut Project) -> R,
    {
        // First cancel any ongoing builds
        {
            let cancel = self.cancel.read().await;
            cancel.cancel();
        }

        // Get write access to the project
        let mut project = self.project.write().await;

        // Call the mutation function
        let result = f(&mut project);

        // Create a new cancellation token for future builds
        {
            let mut cancel = self.cancel.write().await;
            *cancel = CancellationToken::new();
        }

        result
    }
}

// Implement Deref for ProjectView to make it easier to use
impl<'a> std::ops::Deref for ProjectView<'a> {
    type Target = Project;

    fn deref(&self) -> &Self::Target {
        &self.guard
    }
}
