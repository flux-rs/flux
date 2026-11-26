# Installs the latest prebuilt Flux on Windows. Run in PowerShell:
#
#     irm https://raw.githubusercontent.com/flux-rs/flux/main/install.ps1 | iex
#
# To install a given release instead, e.g., `nightly-2026-11-20`, run:
#
#     & ([scriptblock]::Create((irm https://raw.githubusercontent.com/flux-rs/flux/main/install.ps1))) -To nightly-2026-11-20
#
# The script downloads and extracts the release archive, and then runs `cargo flux self install`
# from it, which does the actual installation. Once installed, Flux is updated with
# `cargo flux self update`. See install.sh for Linux and macOS.

# Everything is in a function so that, when the script is run with `iex`, its variables and
# preferences don't leak into the user's session. Errors are thrown instead of calling `exit`,
# which would close the user's window.
function Install-Flux {
    param(
        # The release to install
        [string]$To = "nightly"
    )

    $ErrorActionPreference = "Stop"
    # The progress bar of Invoke-WebRequest makes downloads much slower in Windows PowerShell.
    $ProgressPreference = "SilentlyContinue"

    $ReleasesUrl = "https://github.com/flux-rs/flux/releases/download"
    $InstallGuideUrl = "https://flux-rs.github.io/flux/guide/install.html"

    # Keep in sync with the `build` job of .github/workflows/nightly.yml.
    $Arch = $env:PROCESSOR_ARCHITECTURE
    if ($env:PROCESSOR_ARCHITEW6432) { $Arch = $env:PROCESSOR_ARCHITEW6432 }
    if ($Arch -ne "AMD64") {
        throw "there are no Flux releases for Windows on $Arch, see $InstallGuideUrl to build it from source"
    }
    $Target = "x86_64-pc-windows-msvc"

    if (-not (Get-Command rustup -ErrorAction SilentlyContinue)) {
        throw "rustup is required to install Flux, see https://rustup.rs"
    }
    # The tar that ships with Windows 10 and later. A tar from, e.g., Git for Windows may come first
    # in PATH and doesn't understand Windows paths.
    $Tar = Join-Path $env:SystemRoot "System32\tar.exe"
    if (-not (Test-Path $Tar)) {
        throw "tar is required to install Flux, it ships with Windows 10 (1803) and later"
    }

    # Windows PowerShell 5 doesn't enable TLS 1.2 by default.
    [Net.ServicePointManager]::SecurityProtocol =
        [Net.ServicePointManager]::SecurityProtocol -bor [Net.SecurityProtocolType]::Tls12

    $Tmp = Join-Path ([IO.Path]::GetTempPath()) ("flux-install-" + [Guid]::NewGuid())
    New-Item -ItemType Directory -Path $Tmp | Out-Null
    try {
        $Archive = Join-Path $Tmp "flux-$Target.tar.gz"
        $Url = "$ReleasesUrl/$To/flux-$Target.tar.gz"
        Write-Host "Downloading $Url"
        try {
            Invoke-WebRequest -Uri $Url -OutFile $Archive -UseBasicParsing
        } catch {
            throw "failed to download the release $To, the releases are listed in https://github.com/flux-rs/flux/releases"
        }
        & $Tar -xzf $Archive -C $Tmp
        if ($LASTEXITCODE -ne 0) { throw "failed to extract $Archive" }

        & (Join-Path $Tmp "sysroot\bin\cargo-flux.exe") flux self install
        if ($LASTEXITCODE -ne 0) { throw "failed to install Flux" }
    } finally {
        Remove-Item -Recurse -Force $Tmp -ErrorAction SilentlyContinue
    }
}

Install-Flux @args
