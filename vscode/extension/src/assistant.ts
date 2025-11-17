import {
  commands,
  Disposable,
  Range,
  TextEditor,
  TextEditorRevealType,
  TextEditorSelectionChangeKind,
  Uri,
  ViewColumn,
  WebviewPanel,
  window,
  workspace,
} from "vscode";
import * as fs from "fs";
import * as path from "path";
import { LanguageClient } from "vscode-languageclient/node";

const showLocationDecoration = window.createTextEditorDecorationType({
  backgroundColor: "rgba(246, 185, 77, 0.3)",
});

export class Assistant implements Disposable {
  client: LanguageClient;
  currentParams: SelectionParams;
  currentSelectionId: number;
  disposables: Disposable[];
  distPath: string;
  listener: Disposable;
  panel: WebviewPanel;
  requestViewColumn: number;
  wasShown: boolean;

  constructor(client: LanguageClient, distPath: string) {
    this.client = client;
    this.distPath = distPath;
    this.currentSelectionId = 0;
    this.wasShown = false;
    this.disposables = [
      commands.registerTextEditorCommand(
        "acornprover.showAssistant",
        (editor) => this.show(editor)
      ),

      commands.registerTextEditorCommand(
        "acornprover.toggleAssistant",
        (editor) => this.toggle(editor)
      ),
      window.onDidChangeTextEditorSelection(async (e) => {
        if (
          e.kind === TextEditorSelectionChangeKind.Mouse ||
          e.kind === TextEditorSelectionChangeKind.Keyboard
        ) {
          // We only want to trigger on explicit user actions.
          await this.handleSelection(true);
        }
      }),
      workspace.onDidSaveTextDocument(async () => {
        this.chooseHelp();
        await this.handleSelection(false);
      }),
      window.onDidChangeActiveTextEditor(async () => {
        this.chooseHelp();
      }),
    ];
  }

  sendHelp(help: Help) {
    this.panel.webview.postMessage({ type: "help", help });
  }

  // Sends an appropriate help object, based on the active editor.
  chooseHelp() {
    let editor = window.activeTextEditor;
    if (!editor || !editor.document || !this.panel) {
      return;
    }
    let document = editor.document;
    if (document.languageId !== "acorn") {
      return;
    }

    if (document.uri.scheme !== "file") {
      // This is an untitled file.
      this.sendHelp({ newDocument: true });
      return;
    }

    // Heuristic, just when to stop telling people "type in a theorem now please"
    for (let i = 0; i < document.lineCount; i++) {
      const line = document.lineAt(i);
      let trim = line.text.trim();
      if (
        trim.length > 0 &&
        !trim.startsWith("//") &&
        !trim.startsWith("from") &&
        !trim.startsWith("import")
      ) {
        // There may actually be a selection. But the assistant knows to use the selection result
        // if there is one. So, send the help message for there not being a selection.
        this.sendHelp({ noSelection: true });
        return;
      }
    }

    // This document just doesn't have any real stuff in it.
    this.sendHelp({ newDocument: true });
  }

  // Handles the current selection by sending it to the language server.
  // If 'onSelect' is passed, just the selection changed.
  async handleSelection(onSelect: boolean) {
    try {
      let editor = window.activeTextEditor;
      if (
        !editor ||
        !editor.document ||
        editor.document.languageId !== "acorn" ||
        editor.document.uri.scheme !== "file" ||
        !this.panel
      ) {
        return;
      }

      // Clear any showLocation highlighting
      editor.setDecorations(showLocationDecoration, []);

      let uri = editor.document.uri.toString();
      let selectedLine = editor.selection.start.line;
      let version = editor.document.version;

      // Check if we are just selecting a different part of the same target.
      if (
        onSelect &&
        this.currentParams &&
        this.currentParams.uri === uri &&
        this.currentParams.selectedLine === selectedLine
      ) {
        return;
      }

      let id = this.currentSelectionId + 1;
      let params: SelectionParams = { uri, selectedLine, version, id };

      // This view column is probably the one the user is actively writing in.
      // When in doubt, we can use this view column to do code-writing operations.
      this.requestViewColumn = editor.viewColumn;

      await this.sendSelectionRequest(params);
    } catch (e) {
      console.error("error during update:", e);
    }
  }

  // Sends a selection request to the language server, passing the response on to the webview.
  async sendSelectionRequest(params: SelectionParams) {
    console.log(
      `selection request ${params.id}: ${params.uri} v${params.version} line ${params.selectedLine}`
    );
    this.currentSelectionId = params.id;
    this.currentParams = params;

    while (true) {
      let response: SelectionResponse = await this.client.sendRequest(
        "acorn/selection",
        params
      );

      if (!this.panel || params.id != this.currentSelectionId) {
        // The request is no longer relevant
        return;
      }
      if (response.failure) {
        console.log("selection failure:", response.failure);
        return;
      }

      // Handle loading state - don't send to webview, retry quickly
      if (response.loading) {
        let ms = 50;
        await new Promise((resolve) => setTimeout(resolve, ms));
        if (!this.panel || params.id != this.currentSelectionId) {
          return;
        }
        continue;
      }

      // Always send the response to webview when not loading
      this.panel.webview.postMessage({ type: "selection", response });

      // If building, wait longer and retry
      if (response.building) {
        let ms = 1000;
        await new Promise((resolve) => setTimeout(resolve, ms));
        if (!this.panel || params.id != this.currentSelectionId) {
          return;
        }
        continue;
      }

      // The selection request is complete (not loading, not building)
      return;
    }
  }

  // Handles messages from the webview.
  async handleWebviewMessage(message: any) {
    try {
      if (message.command === "showLocation") {
        await this.showLocation(message.uri, message.range);
        return;
      }

      console.log("unhandled message:", message);
    } catch (e) {
      console.error("error handling webview message:", e);
    }
  }

  // Heuristically find an editor for the given uri and focus it.
  // If we don't have one open already, open a new one.
  async focusEditor(uri: string): Promise<TextEditor> {
    // Ideally we use an editor that's already visible
    for (let editor of window.visibleTextEditors) {
      if (editor.document.uri.toString() === uri) {
        await window.showTextDocument(editor.document, editor.viewColumn);
        return editor;
      }
    }

    // If the document is open but not visible, we have to guess a view column.
    for (let document of workspace.textDocuments) {
      if (document.uri.toString() === uri) {
        return window.showTextDocument(document, this.requestViewColumn);
      }
    }

    // If the document is not open, open it as a preview.
    let doc = await workspace.openTextDocument(Uri.parse(uri));
    return window.showTextDocument(doc, {
      viewColumn: this.requestViewColumn,
      preview: true,
    });
  }

  // Show a particular location in the codebase.
  async showLocation(uri: string, range: Range) {
    let editor = await this.focusEditor(uri);

    editor.setDecorations(showLocationDecoration, [range]);
    editor.revealRange(range, TextEditorRevealType.InCenterIfOutsideViewport);
  }

  // Show the assistant if it hasn't been shown for this workspace before, if the
  // active editor is an Acorn file.
  // Triggered by interacting with an Acorn document for the first time.
  maybeShow() {
    if (this.wasShown) {
      return;
    }
    let editor = window.activeTextEditor;
    if (!editor || editor.document.languageId !== "acorn") {
      return;
    }
    this.show(editor);
  }

  // Show the search panel itself.
  show(editor: TextEditor) {
    this.wasShown = true;
    let column =
      editor && editor.viewColumn ? editor.viewColumn + 1 : ViewColumn.Two;
    if (column === 4) {
      column = ViewColumn.Three;
    }
    if (this.panel) {
      this.panel.reveal(column);
      return;
    }
    this.panel = window.createWebviewPanel(
      "acornAssistant",
      "Acorn Assistant",
      { viewColumn: column, preserveFocus: true },
      {
        enableFindWidget: true,
        retainContextWhenHidden: true,
        enableScripts: true,
        localResourceRoots: [Uri.file(this.distPath)],
      }
    );

    this.listener = this.panel.webview.onDidReceiveMessage(
      this.handleWebviewMessage,
      this
    );

    this.panel.onDidDispose(() => {
      this.listener.dispose();
      this.listener = null;
      this.panel = null;
    });

    // Set the webview's initial content
    let distPathInWebview = this.panel.webview.asWebviewUri(
      Uri.file(this.distPath)
    );
    let indexPath = Uri.file(path.join(this.distPath, "index.html"));
    let html = fs.readFileSync(indexPath.fsPath, "utf8");
    // Inject a new base href tag
    let injected = html.replace(
      "<head>",
      `<head>\n<base href="${distPathInWebview}/">`
    );
    this.panel.webview.html = injected;

    // Always reissue the selection request on panel open.
    this.chooseHelp();
    this.currentParams = null;
    this.handleSelection(false);
  }

  toggle(editor: TextEditor) {
    if (this.panel) {
      this.panel.dispose();
      this.panel = null;
      return;
    }

    this.show(editor);
  }

  dispose() {
    for (let subscription of this.disposables) {
      subscription.dispose();
    }
    if (this.panel) {
      this.panel.dispose();
    }
  }
}
