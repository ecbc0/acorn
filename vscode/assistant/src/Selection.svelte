<script lang="ts">
  import Goal from "./Goal.svelte";

  export let selectionResponse: SelectionResponse;
  export let showLocation: (uri: string, range: Range) => void;

  function pluralize(n: number, noun: string): string {
    let word = n === 1 ? noun : noun + "s";
    return `${n} ${word}`;
  }
</script>

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
    The detailed proof has {pluralize(selectionResponse.steps.length, "step")}:
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
