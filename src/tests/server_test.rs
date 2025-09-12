use crate::server::{AcornLanguageServer, LspClient, ServerArgs};
use assert_fs::fixture::ChildPath;
use assert_fs::prelude::*;
use assert_fs::TempDir;
use std::sync::Arc;
use tower_lsp::lsp_types::{Diagnostic, Url};

/// Mock implementation of LspClient for testing
#[derive(Clone)]
struct MockClient {
    // We can add fields here later to track what methods were called
}

#[async_trait::async_trait]
impl LspClient for MockClient {
    async fn publish_diagnostics(
        &self,
        _uri: Url,
        _diagnostics: Vec<Diagnostic>,
        _version: Option<i32>,
    ) {
        // For now, do nothing
    }
}

/// Test fixture that sets up an Acorn language server with a temp directory.
/// Automatically cleans up when dropped.
struct TestFixture {
    _temp_dir: TempDir, // Must keep this alive or the directory gets deleted!
    pub src_dir: ChildPath,
    pub build_dir: ChildPath,
    _client: Arc<MockClient>,
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

        let client = Arc::new(MockClient {});
        let server = AcornLanguageServer::new(client.clone(), &args);

        TestFixture {
            _temp_dir: temp_dir,
            src_dir,
            build_dir,
            _client: client,
            server,
        }
    }

    /// Converts a relative path to a file:// URL that can be used with set_full_text
    fn url(&self, path: &str) -> Url {
        let full_path = self.src_dir.path().join(path);
        Url::from_file_path(full_path).unwrap()
    }
}

#[tokio::test]
async fn test_server_basic() {
    let fx = TestFixture::new();

    // Use the url method to get a proper file:// URL and call set_full_text
    let url = fx.url("foo.ac");
    fx.server
        .set_full_text(url, "theorem foo { true }".to_string(), Some(1))
        .await;

    // Verify the server processed the project
    assert!(fx.src_dir.path().exists());
    assert!(fx.build_dir.path().exists());
}
