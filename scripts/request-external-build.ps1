$ErrorActionPreference = "Stop"

$repo = if ($env:LEGAL_MATH_MODELING_ROOT) {
    (Resolve-Path -LiteralPath $env:LEGAL_MATH_MODELING_ROOT).Path
} else {
    (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot "..")).Path
}
$python = if ($env:LEGAL_MATH_PYTHON) { $env:LEGAL_MATH_PYTHON } else { "python" }
$timestamp = Get-Date -Format "yyyyMMdd-HHmmss"
$outputDirectory = Join-Path $repo "build-logs\$timestamp"

& $python (Join-Path $repo "scripts\generate_formal_release_certificate.py") `
    --repo-root $repo `
    --check-inventories `
    --run-gates `
    --output-dir "build-logs\$timestamp"
$generationExitCode = $LASTEXITCODE

$commit = (& git -C $repo rev-parse HEAD).Trim()
$certificate = Join-Path $outputDirectory "formal-release-certificate-$commit.json"
if (-not (Test-Path -LiteralPath $certificate)) {
    throw "Certificate was not generated: $certificate"
}

& $python (Join-Path $repo "scripts\verify_formal_release_certificate.py") `
    $certificate `
    --repo-root $repo `
    --artifact-dir $outputDirectory
$verificationExitCode = $LASTEXITCODE

if ($generationExitCode -ne 0 -or $verificationExitCode -ne 0) {
    exit 1
}

Write-Output $certificate
