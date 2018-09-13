<?php
ob_start('ob_gzhandler');
error_reporting(E_ALL | E_STRICT);
error_reporting(E_ERROR | E_WARNING | E_PARSE);
ini_set('display_errors',1);


class MyDB extends SQLite3 {
  function __construct() {
     $this->open('test.db');
  }
}

$sql = new MyDB();
if(!$sql) {
  echo $sql->lastErrorMsg();
} else {
  #echo "Opened database successfully\n";
  #print_r($sql);
}
?>
