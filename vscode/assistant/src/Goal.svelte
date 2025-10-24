<script lang="ts">
  export let goalName: string | null;
  export let goalRange: Range | null;
  export let uri: string;
  export let showLocation: (uri: string, range: Range) => void;

  function callback() {
    if (goalRange !== null) {
      showLocation(uri, goalRange);
    }
  }
</script>

{#if goalName === null}
  <span class="header">There is no goal.</span>
{:else if goalRange === null}
  <span class="header">{goalName}</span>
{:else}
  <span class="header goal-link" on:click={callback}
    >{goalName}</span
  >
{/if}

<style>
  .goal-link {
    cursor: pointer;
  }

  .goal-link:hover {
    text-decoration: underline;
  }
</style>
