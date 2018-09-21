<?php
include "connect.php";

function fill_gitrevs($sql)
{
    $query = "select `gitrev` from `solverRun` group by `gitrev`;";
    $stmt = $sql->prepare($query);
    if (!$stmt) {
        die("Cannot prepare statement");
    }
    $result = $stmt->execute();
    $json = array();

    while($arr=$result->fetchArray(SQLITE3_ASSOC))
    {
         $data = array(
            'gitrev' => $arr["gitrev"],
        );
        array_push($json, $data);
    }
    $jsonstring = json_encode($json);
    echo $jsonstring;
    $stmt->close();
}
fill_gitrevs($sql);
?>
