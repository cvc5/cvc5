Add-Type -AssemblyName System.IO.Compression.FileSystem

function Unzip
{
    param([string]$zipfile, [string]$outpath)

    [System.IO.Compression.ZipFile]::ExtractToDirectory($zipfile, $outpath)
}

$wc = New-Object System.Net.WebClient
$wc.DownloadFile("http://bit.ly/1JPHkL3", "C:\projects\cryptominisat\boost_1_59_0.zip")

Unzip "C:\projects\cryptominisat\boost_1_59_0.zip" "C:\projects\cryptominisat"
