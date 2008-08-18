<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <meta http-equiv="Content-Type" content="text/php/html; charset=utf-8" />
    <title>Test Execution</title>
    <link rel="stylesheet" href="main.css" type="text/css" />
  </head>
  
  <body>
    <?php
      $f = $_REQUEST[formula];
      $l = $_REQUEST[logic];
      $command = "./coloss.cgi ".$l." -t "."\"".$f."\"";
      $output = shell_exec($command);
      echo "<pre>$output</pre>";
    ?>
    <br>
    <a href="tool.html">Back</a>
  </body>
</html>
