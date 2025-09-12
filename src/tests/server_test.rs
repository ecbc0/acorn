use crate::server::{AcornLanguageServer, LspClient, ServerArgs};
use assert_fs::fixture::ChildPath;
use assert_fs::prelude::*;
use assert_fs::TempDir;
use std::sync::Arc;
use tower_lsp::lsp_types::{
    Diagnostic, DidChangeTextDocumentParams, DidOpenTextDocumentParams, DidSaveTextDocumentParams,
    TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentItem, Url,
    VersionedTextDocumentIdentifier,
};
use tower_lsp::LanguageServer;

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

    let text1 = "theorem foo { true }";
    let text2 = "theorem bar { true }";

    let url = fx.url("foo.ac");

    // First, open the document with text1
    fx.server
        .did_open(DidOpenTextDocumentParams {
            text_document: TextDocumentItem {
                uri: url.clone(),
                language_id: "acorn".to_string(),
                version: 1,
                text: text1.to_string(),
            },
        })
        .await;

    // Then, change the document to text2 (replacing entire content)
    fx.server
        .did_change(DidChangeTextDocumentParams {
            text_document: VersionedTextDocumentIdentifier {
                uri: url.clone(),
                version: 2,
            },
            content_changes: vec![TextDocumentContentChangeEvent {
                range: None,
                range_length: None,
                text: text2.to_string(),
            }],
        })
        .await;

    // Finally, save the document with text2
    fx.server
        .did_save(DidSaveTextDocumentParams {
            text_document: TextDocumentIdentifier { uri: url.clone() },
            text: Some(text2.to_string()),
        })
        .await;

    // Verify the server processed the project
    assert!(fx.src_dir.path().exists());
    assert!(fx.build_dir.path().exists());
}
