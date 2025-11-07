#!/bin/bash

# Script to calculate the byte change of the current git repo compared to main branch

# Get the main branch name (usually 'main' or 'master')
MAIN_BRANCH=$(git symbolic-ref refs/remotes/origin/HEAD 2>/dev/null | sed 's@^refs/remotes/origin/@@')
if [ -z "$MAIN_BRANCH" ]; then
    MAIN_BRANCH="master"
fi

# Get all changed files compared to main branch
# This includes: committed changes on current branch + staged + unstaged changes
CHANGED_FILES=$(git diff --name-only $MAIN_BRANCH 2>/dev/null | sort -u)

if [ -z "$CHANGED_FILES" ]; then
    echo "No changes detected compared to $MAIN_BRANCH branch"
    exit 0
fi

# Calculate total size of all files in main branch
echo "Calculating total repository size in $MAIN_BRANCH branch..."
MAIN_BRANCH_TOTAL=$(git ls-tree -r $MAIN_BRANCH | awk '{print $4, $3}' | while read size hash; do git cat-file -s $hash 2>/dev/null || echo 0; done | awk '{sum+=$1} END {print sum}')

# Calculate total size of all files in current working directory
echo "Calculating total repository size in current state..."
CURRENT_TOTAL=$(git ls-files | xargs -I{} sh -c 'if [ -f "{}" ]; then wc -c < "{}"; else echo 0; fi' | awk '{sum+=$1} END {print sum}')

# Calculate bytes added and removed in changed files
BYTES_ADDED=0
BYTES_REMOVED=0

echo "Processing changed files compared to $MAIN_BRANCH branch..."
echo ""

while IFS= read -r file; do
    echo "Processing: $file"

    if [ -f "$file" ]; then
        # File exists in current state
        CURRENT_SIZE=$(wc -c < "$file" 2>/dev/null || echo 0)

        # Get file size in main branch (if it exists there)
        MAIN_SIZE=$(git show "$MAIN_BRANCH:$file" 2>/dev/null | wc -c)
        if [ $? -ne 0 ]; then
            # File doesn't exist in main branch (newly added)
            MAIN_SIZE=0
        fi

        DIFF=$((CURRENT_SIZE - MAIN_SIZE))
        if [ $DIFF -gt 0 ]; then
            BYTES_ADDED=$((BYTES_ADDED + DIFF))
        else
            BYTES_REMOVED=$((BYTES_REMOVED + (-DIFF)))
        fi
    else
        # File was deleted
        MAIN_SIZE=$(git show "$MAIN_BRANCH:$file" 2>/dev/null | wc -c)
        if [ $? -eq 0 ]; then
            BYTES_REMOVED=$((BYTES_REMOVED + MAIN_SIZE))
        fi
    fi
done <<< "$CHANGED_FILES"

echo ""

# Calculate net change
NET_CHANGE=$((BYTES_ADDED - BYTES_REMOVED))

# Calculate percentage change
if [ $MAIN_BRANCH_TOTAL -gt 0 ]; then
    PERCENT_CHANGE=$(awk "BEGIN {printf \"%.2f\", ($NET_CHANGE / $MAIN_BRANCH_TOTAL) * 100}")
else
    PERCENT_CHANGE="N/A"
fi

echo "Byte changes compared to $MAIN_BRANCH branch:"
printf "  Repository size in %s: %10d bytes\n" "$MAIN_BRANCH" "$MAIN_BRANCH_TOTAL"
printf "  Repository size now:       %10d bytes\n" "$CURRENT_TOTAL"
printf "  Bytes added:               %10s\n" "+$BYTES_ADDED"
printf "  Bytes removed:             %10s\n" "-$BYTES_REMOVED"
printf "  Net change:                %10d bytes (%s%%)\n" "$NET_CHANGE" "$PERCENT_CHANGE"
