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
    _temp_dir: TempDir,  // Must keep this alive or the directory gets deleted!
    pub src_dir: ChildPath,
    pub build_dir: ChildPath,
    _client: Arc<MockClient>,
    _server: AcornLanguageServer,
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
            _server: server,
        }
    }
}

#[tokio::test]
async fn test_server_basic() {
    let fx = TestFixture::new();

    fx.src_dir
        .child("foo.ac")
        .write_str(
            r#"
        theorem simple_truth {
            true
        }
        "#,
        )
        .unwrap();

    // For now, just verify that we can create the server
    // The server should have found our project structure
    assert!(fx.src_dir.path().exists());
    assert!(fx.build_dir.path().exists());
}
