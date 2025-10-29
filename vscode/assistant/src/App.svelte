<script context="module">
  let vscode = acquireVsCodeApi();
</script>

<script lang="ts">
  import { onMount } from "svelte";
  import Goal from "./Goal.svelte";

  // These are updated to reflect the last valid responses from the extension.
  let selectionResponse: SelectionResponse | null = null;
  let help: Help | null = null;

  function handleSelectionResponse(response: SelectionResponse) {
    if (response.failure || response.goalName === null) {
      // Failure responses should not reach this point.
      console.error("unexpected upstream failure:", response.failure);
      return;
    }

    selectionResponse = response;
  }

  onMount(() => {
    window.addEventListener("message", (event) => {
      if (event.data.type === "selection") {
        handleSelectionResponse(event.data.response);
        return;
      }
      if (event.data.type === "help") {
        help = event.data.help;
        return;
      }
      console.error("unexpected message type:", event.data.type);
    });
  });

  function showLocation(uri: string, range: Range) {
    vscode.postMessage({ command: "showLocation", uri, range });
  }

  function pluralize(n: number, noun: string): string {
    let word = n === 1 ? noun : noun + "s";
    return `${n} ${word}`;
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
      {#if selectionResponse.building}
        Building...
      {:else}
        We don't have a proof for this goal yet.
      {/if}
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
  {:else}
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

  td:first-child {
    white-space: pre-wrap;
    font-family: monospace;
  }
</style>
