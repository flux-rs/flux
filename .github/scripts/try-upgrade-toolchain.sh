#!/usr/bin/env bash
set -eu

end_toolchain="${1:-}"
days_per_iter="${2:-1}"

echo ~/.cargo/bin >> $GITHUB_PATH

git config --global user.email "github-actions[bot]@users.noreply.github.com"
git config --global user.name "github-actions[bot]"

cd flux

start_toolchain=$(grep ^channel rust-toolchain.toml | sed 's/.*nightly-\([0-9\-]*\)"/\1/')

# Use argument if provided, otherwise fetch latest
if [ -n "$end_toolchain" ]; then
  :
else
  end_toolchain=$(curl -s https://static.rust-lang.org/dist/channel-rust-nightly.toml | grep "^date" | head -n 1 | cut -d'"' -f2)
  if [ -z "$end_toolchain" ]; then
    echo "Could not determine latest nightly version."
    exit 1
  fi
fi
echo "Start toolchain: $start_toolchain"
echo "End toolchain: $end_toolchain"
echo "Days per iteration: $days_per_iter"


curr_toolchain=$start_toolchain
while true; do
  curr_toolchain=$(date -I -d "$curr_toolchain + $days_per_iter day")
  if [[ "$curr_toolchain" > "$end_toolchain" ]]; then
    curr_toolchain="$end_toolchain"
  fi

  echo "::group::Upgrade to nightly-$curr_toolchain"
  sed -i "s/^channel = \"nightly-[0-9\-]*\"/channel = \"nightly-$curr_toolchain\"/" rust-toolchain.toml
  git add rust-toolchain.toml
  git commit -m "Upgrade to nightly-$curr_toolchain"
  cargo clean
  echo "::endgroup::"

  echo "::group::Check (nightly-$curr_toolchain)"
  cargo check
  echo "::endgroup::"

  echo "::group::Tests (nightly-$curr_toolchain)"
  cargo x test
  echo "::endgroup::"

  echo "::group::Install (nightly-$curr_toolchain)"
  cargo x install
  echo "::endgroup::"

  echo "::group::Vtock (nightly-$curr_toolchain)"
  cd ../tock
  cargo flux clean
  cargo flux -p kernel
  cd ../flux
  echo "::endgroup::"

  if [[ "$curr_toolchain" == "$end_toolchain" ]]; then
    break
  fi
done
