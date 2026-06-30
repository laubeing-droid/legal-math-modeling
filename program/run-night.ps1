$ErrorActionPreference = "Continue"

$Root = if ($env:LEGAL_MATH_MODELING_ROOT) { $env:LEGAL_MATH_MODELING_ROOT } else { "D:\Codex\数学证明\legal-math-modeling" }
$Program = Join-Path $Root "program"
$RunId = Get-Date -Format "yyyyMMdd-HHmmss"
$RunDir = Join-Path $Program "runs\$RunId"

New-Item -ItemType Directory -Force -Path $RunDir | Out-Null

$GoalFile = Join-Path $Program "MEGA_GOAL.md"
$EventFile = Join-Path $RunDir "events.jsonl"
$FinalFile = Join-Path $RunDir "final.md"
$ErrorFile = Join-Path $RunDir "stderr.log"

Set-Location $Root

Get-Content $GoalFile -Raw |
  codex exec - `
    --sandbox workspace-write `
    --json `
    --output-last-message $FinalFile `
  2> $ErrorFile |
  Tee-Object $EventFile

$exitCode = $LASTEXITCODE

@{
  run_id = $RunId
  exit_code = $exitCode
  finished_at = (Get-Date).ToString("o")
  events = $EventFile
  final = $FinalFile
  stderr = $ErrorFile
} | ConvertTo-Json | Set-Content (Join-Path $RunDir "run-summary.json")

exit $exitCode
