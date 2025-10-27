<script context="module">
  let vscode = acquireVsCodeApi();
</script>

<script lang="ts">
  import { onMount } from "svelte";
  import Goal from "./Goal.svelte";
  import ProofStep from "./ProofStep.svelte";

  // These are updated to reflect the last valid responses from the extension.
  let searchResponse: SearchResponse | null = null;
  let selectionResponse: SelectionResponse | null = null;
  let infoResult: InfoResult | null = null;
  let help: Help | null = null;

  function handleSearchResponse(response: SearchResponse) {
    if (response.failure || response.goalName === null) {
      // Failure responses should not reach this point.
      console.error("unexpected upstream failure:", response.failure);
      return;
    }

    if (searchResponse !== null && searchResponse.id !== response.id) {
      // A successful search invalidate the other data
      infoResult = null;
    }

    searchResponse = response;
  }

  function handleSelectionResponse(response: SelectionResponse) {
    if (response.failure || response.goalName === null) {
      // Failure responses should not reach this point.
      console.error("unexpected upstream failure:", response.failure);
      return;
    }

    if (selectionResponse !== null && selectionResponse.id !== response.id) {
      // A successful selection invalidates the other data
      infoResult = null;
    }

    selectionResponse = response;
  }

  function handleInfoResponse(response: InfoResponse) {
    // Only accept info responses that match the current search response.
    if (
      searchResponse === null ||
      response.result === null ||
      response.searchId != searchResponse.id
    ) {
      return;
    }
    infoResult = response.result;
  }

  onMount(() => {
    window.addEventListener("message", (event) => {
      if (event.data.type === "search") {
        handleSearchResponse(event.data.response);
        return;
      }
      if (event.data.type === "selection") {
        handleSelectionResponse(event.data.response);
        return;
      }
      if (event.data.type === "info") {
        handleInfoResponse(event.data.response);
        return;
      }
      if (event.data.type === "help") {
        help = event.data.help;
        return;
      }
      console.error("unexpected message type:", event.data.type);
    });
  });

  function insertProof() {
    if (
      searchResponse === null ||
      searchResponse.status.code === null ||
      searchResponse.status.code.length === 0
    ) {
      console.log("cannot insert proof");
      return;
    }
    vscode.postMessage({
      command: "insertProof",
      uri: searchResponse.uri,
      version: searchResponse.version,
      line: searchResponse.proofInsertionLine,
      insertBlock: searchResponse.insertBlock,
      code: searchResponse.status.code,
    });
  }

  function clauseClick(id: number) {
    if (searchResponse === null) {
      return;
    }
    let params: InfoParams = {
      searchId: searchResponse.id,
      clauseId: id,
    };
    vscode.postMessage({ command: "infoRequest", params });
  }

  function randomClause() {
    if (searchResponse === null || searchResponse.status.numActivated === 0) {
      return;
    }

    // Pick a random activated clause
    let id = Math.floor(Math.random() * searchResponse.status.numActivated);
    clauseClick(id);
  }

  function showLocation(uri: string, range: Range) {
    vscode.postMessage({ command: "showLocation", uri, range });
  }

  function pluralize(n: number, noun: string): string {
    let word = n === 1 ? noun : noun + "s";
    return `${n} ${word}`;
  }

  function spaces(n: number): string {
    return "\u00A0".repeat(n);
  }
</script>

<main>
  {#if selectionResponse !== null && selectionResponse.goalName !== null}
    <Goal
      goalName={selectionResponse.goalName}
      goalRange={selectionResponse.goalRange}
      uri={selectionResponse.uri}
      {showLocation}
    />
    <hr />
    <br />
    {#if selectionResponse.steps === null}
      We don't have a proof for this goal yet.
      <br />
    {:else if selectionResponse.steps.length === 0}
      Trivial.
      <br />
    {:else}
      <div class="block">
        <br />
        The detailed proof has {pluralize(
          selectionResponse.steps.length,
          "step"
        )}:
        <br /><br />
        <table>
          <tr>
            <th>Statement</th>
            <th>Reason</th>
          </tr>
          {#each selectionResponse.steps as step}
            <tr>
              <td>{step.statement}</td>
              <td>
                {#if step.location !== null}
                  <span
                    class="preview-link"
                    on:click={() => {
                      if (step.location !== null) {
                        showLocation(step.location.uri, step.location.range);
                      }
                    }}>{step.reason}</span
                  >
                {:else}
                  <span>{step.reason}</span>
                {/if}
              </td>
            </tr>
          {/each}
        </table>
        <br />
      </div>
    {/if}
    <br />
    <hr />
  {:else if searchResponse === null || searchResponse.goalName === null}
    {#if help !== null && help.noSelection}
      Select a proposition to see its proof.
    {:else if help !== null && help.newDocument}
      Enter a theorem that you want to prove.
      <br /><br />
      When you're ready, save the file to verify it.
    {:else}
      <!-- Default message to be shown when we don't even have an Acorn file open. -->
      This is the Acorn Assistant.
      <br /><br />
      To get started, open an Acorn file, or create a new one.
      <br /><br />
      An Acorn file has to have a .ac extension.
    {/if}
    <br /><br />
    For help, see the
    <a href="https://acornprover.org">documentation</a>.
  {:else}
    <Goal
      goalName={searchResponse.goalName}
      goalRange={searchResponse.goalRange}
      uri={searchResponse.uri}
      {showLocation}
    />
    <hr />
    <br />
    {#if searchResponse.status.outcome === null}
      Working...
    {:else if searchResponse.status.outcome === "Inconsistent"}
      Local assumptions are inconsistent.
      <br />
      If this is a proof by contradiction, put a `false` at the end of this block.
      <br />
      If there shouldn't be a contradiction, please report a bug!
    {:else if searchResponse.status.steps === null}
      We could not find a proof.
    {:else if searchResponse.status.code === null}
      Error during code generation:
      <br />
      {spaces(4)}{searchResponse.status.codeError}
    {:else if !searchResponse.status.needsSimplification}
      The proposition follows trivially.
    {:else if searchResponse.status.code.length === 0}
      We found a proof, but it needs to be simplified, and we couldn't decide
      how to simplify it. Sorry!
    {:else}
      The proof needs to be simplified. Try this:
      <br />
      {#each searchResponse.status.code as code}
        <br />
        {spaces(4)}{code}
      {/each}
      <br /><br />
      <button on:click={insertProof}>Insert code</button>
    {/if}
    <br />

    {#if searchResponse.status.steps !== null}
      <div class="block">
        <br />
        The full proof has {pluralize(
          searchResponse.status.steps.length,
          "step"
        )}:
        <br />
        {#each searchResponse.status.steps as step}
          <br />
          <ProofStep {step} {clauseClick} {showLocation} />
        {/each}
      </div>
    {/if}
    <br />
    <hr />
    <div class="block">
      <br />
      <button
        on:click={() => {
          infoResult = null;
        }}>Statistics</button
      >
      <button on:click={randomClause}>Random clause</button>
      <br /><br />
      {#if infoResult === null}
        <span
          >Prover status: {searchResponse.status.outcome === null
            ? "Working..."
            : searchResponse.status.outcome}</span
        >
        <br />
        <span>Activated clauses: {searchResponse.status.numActivated}</span>
      {:else}
        <ProofStep step={infoResult.step} {clauseClick} {showLocation} />
        <br />
        {#if infoResult.consequences.length === 0}
          There are no consequences.
        {:else}
          Consequences:<br />
          {#each infoResult.consequences as step}
            <br />
            <ProofStep {step} {clauseClick} {showLocation} />
          {/each}
          {#if infoResult.numConsequences > infoResult.consequences.length}
            <br />
            Truncated. Showing {infoResult.consequences.length} out of {infoResult.numConsequences}
            clauses.
          {/if}
        {/if}
      {/if}
    </div>
    <br />
  {/if}
</main>

<style>
  .preview-link {
    cursor: pointer;
    color: var(--vscode-textLink-foreground);
  }

  .preview-link:hover {
    text-decoration: underline;
  }

  table {
    width: 100%;
    table-layout: fixed;
    border-spacing: 0;
  }

  th:first-child,
  td:first-child {
    width: 66.66%;
  }

  th:last-child,
  td:last-child {
    width: 33.33%;
  }

  td {
    padding-top: 0.5em;
    padding-bottom: 0.5em;
  }

  th {
    padding-bottom: 0.5em;
    text-align: left;
  }
</style>
