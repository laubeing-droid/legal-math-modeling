# request-external-build.ps1
# Run in PowerShell to complete the Lean 4 lake build externally.
# Do NOT run lake clean first. Incremental cache preserved.

$repo = if ($env:LEGAL_MATH_MODELING_ROOT) { $env:LEGAL_MATH_MODELING_ROOT } else { "D:\Codex\数学证明\legal-math-modeling" }
$lakeDir = "$repo\proofs\lean\juris_lean"
$ts = Get-Date -Format "yyyyMMdd-HHmmss"
$logDir = "$repo\build-logs\$ts"
New-Item -ItemType Directory -Force -Path $logDir | Out-Null

$logFile = "$logDir\lake-build.log"
$resultFile = "$logDir\build-result.json"

$commit = (git -C $repo rev-parse HEAD)

Write-Host "=== External Lake Build ==="
Write-Host "Commit: $commit"
Write-Host "Log:    $logFile"
Write-Host ""

$started = Get-Date
Push-Location $lakeDir
try {
    lake build 2>&1 | Tee-Object $logFile
    $exitCode = $LASTEXITCODE
} finally {
    Pop-Location
}
$finished = Get-Date

$result = @{
    exit_code   = $exitCode
    git_commit  = $commit
    started_at  = $started.ToString("o")
    finished_at = $finished.ToString("o")
    duration_s  = [math]::Round(($finished - $started).TotalSeconds, 1)
    log_sha256  = (Get-FileHash $logFile -Algorithm SHA256).Hash
    lake_dir    = $lakeDir
} | ConvertTo-Json -Depth 2

[System.IO.File]::WriteAllText(
    $resultFile,
    $result,
    [System.Text.UTF8Encoding]::new($false)
)

Write-Host "Exit: $exitCode  Time: $($result.duration_s)s  Result: $resultFile"
if ($exitCode -ne 0) { Write-Host "BUILD FAILED. Check log."; exit $exitCode }
Write-Host "BUILD OK. Run: python $repo\scripts\finalize-external-build.py $resultFile"
