$ErrorActionPreference = "Stop"
$PSNativeCommandUseErrorActionPreference = $false

$Env:http_proxy = "http://127.0.0.1:7890"
$Env:https_proxy = "http://127.0.0.1:7890"

Set-Location (Join-Path $PSScriptRoot "..\book_zh")
& lake exe fp-lean --depth 2 --without-html-single --verbose 2>&1 | Tee-Object -FilePath "..\book_zh_build.log"
exit $LASTEXITCODE
