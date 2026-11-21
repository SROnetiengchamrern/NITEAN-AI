param(
    [Parameter(Mandatory = $true)]
    [string]$SpecPath
)

Add-Type -AssemblyName PresentationCore
Add-Type -AssemblyName PresentationFramework
Add-Type -AssemblyName WindowsBase

$spec = Get-Content -LiteralPath $SpecPath -Encoding UTF8 -Raw | ConvertFrom-Json
$width = [int]$spec.frameWidth
$height = [int]$spec.frameHeight
$culture = [System.Globalization.CultureInfo]::GetCultureInfo("km-KH")
$flow = [System.Windows.FlowDirection]::LeftToRight
$typeface = New-Object System.Windows.Media.Typeface "Leelawadee UI"
$center = [System.Windows.Media.Color]::FromRgb(46, 34, 26)
$edge = [System.Windows.Media.Color]::FromRgb(10, 8, 7)
$goldBrush = New-Object System.Windows.Media.SolidColorBrush ([System.Windows.Media.Color]::FromRgb(224, 162, 74))
$creamBrush = New-Object System.Windows.Media.SolidColorBrush ([System.Windows.Media.Color]::FromRgb(244, 239, 232))
$shadowBrush = New-Object System.Windows.Media.SolidColorBrush ([System.Windows.Media.Color]::FromArgb(210, 0, 0, 0))

function Fit-StoryText([string]$content, [double]$size, $brush, [double]$boxWidth, [double]$maxHeight) {
    $fitted = $size
    $text = $null
    while ($fitted -ge 22) {
        $text = New-StoryText $content $fitted $brush $boxWidth
        if ($text.Height -le $maxHeight) {
            return $text
        }
        $fitted -= 4
    }
    return $text
}

function New-StoryText([string]$content, [double]$size, $brush, [double]$boxWidth) {
    $text = New-Object System.Windows.Media.FormattedText(
        $content,
        $culture,
        $flow,
        $typeface,
        $size,
        $brush,
        1.0
    )
    $text.MaxTextWidth = $boxWidth
    $text.TextAlignment = [System.Windows.TextAlignment]::Center
    return $text
}

function Draw-StoryText($dc, $text, [double]$x, [double]$y, $fill) {
    $text.SetForegroundBrush($shadowBrush)
    $dc.DrawText($text, (New-Object System.Windows.Point ($x + 2), ($y + 3)))
    $text.SetForegroundBrush($fill)
    $dc.DrawText($text, (New-Object System.Windows.Point $x, $y))
}

foreach ($slide in @($spec.slides)) {
    $visual = New-Object System.Windows.Media.DrawingVisual
    $dc = $visual.RenderOpen()
    $rect = New-Object System.Windows.Rect 0, 0, $width, $height
    $glow = New-Object System.Windows.Media.RadialGradientBrush $center, $edge
    $glow.GradientOrigin = New-Object System.Windows.Point 0.5, 0.38
    $glow.Center = New-Object System.Windows.Point 0.5, 0.42
    $glow.RadiusX = 0.72
    $glow.RadiusY = 0.78
    $dc.DrawRectangle($glow, $null, $rect)

    $body = [string]$slide.body
    $isTitle = [string]$slide.style -eq "title"
    if ($isTitle) {
        $text = Fit-StoryText $body 58 $goldBrush 1080 480
        $y = [Math]::Max(80, ($height - $text.Height) / 2)
        Draw-StoryText $dc $text 100 $y $goldBrush
    }
    else {
        $text = Fit-StoryText $body 44 $creamBrush 1080 520
        $y = [Math]::Max(80, ($height - $text.Height) / 2)
        Draw-StoryText $dc $text 100 $y $creamBrush
    }
    $dc.Close()

    $bitmap = New-Object System.Windows.Media.Imaging.RenderTargetBitmap $width, $height, 96, 96, ([System.Windows.Media.PixelFormats]::Pbgra32)
    $bitmap.Render($visual)
    $encoder = New-Object System.Windows.Media.Imaging.PngBitmapEncoder
    $encoder.Frames.Add([System.Windows.Media.Imaging.BitmapFrame]::Create($bitmap))
    $stream = [System.IO.File]::Open([string]$slide.file, "Create")
    $encoder.Save($stream)
    $stream.Close()
}
