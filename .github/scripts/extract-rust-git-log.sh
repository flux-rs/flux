#!/bin/bash

# Script to extract git commit logs between two commits and format them as GitHub URLs
# Usage: ./extract-rust-git-log.sh <prev_commit_hash> <last_commit_hash>

set -e

if [ $# -ne 2 ]; then
    echo "Usage: $0 <prev_commit_hash> <last_commit_hash>"
    exit 1
fi

prev_commit_hash=$1
last_commit_hash=$2

git log --oneline --ancestry-path "$prev_commit_hash..$last_commit_hash" | while read -r commit; do
    # If we find a PR number print that as it gives more useful information in the github UI
    if [[ $commit =~ \#([0-9]+) ]]; then
        pr_number="${BASH_REMATCH[1]}"
        echo "* rust-lang/rust#$pr_number"
    else
        echo "* https://github.com/rust-lang/rust/commit/$commit"
    fi
done
