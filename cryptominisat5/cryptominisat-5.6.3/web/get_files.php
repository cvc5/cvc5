<?php
include "connect.php";

$unfinished = $_GET["unfinish"] == "true";
$sat = $_GET["sat"] == "true";
$unsat = $_GET["unsat"] == "true";
# $gitrev = 'f3fc12d8582dcada94802882c6108d10b3581cfa';
$unfinished = True;
$sat = True;
$unsat = True;

$json = array();
function get_files_for_gitrev($sat, $unsat, $unfinished)
{
    global $sql, $json;

    $toadd = "(";
    $num = 0;
    if ($unfinished) {
        $num++;
        $toadd .= "finishup.status is NULL";
    }
    if ($sat) {
        if ($num >0 ) $toadd .= " or ";
        $num++;
        $toadd .= "finishup.status = 'l_True'";
    }
    if ($unsat) {
        if ($num >0 ) $toadd .= " or ";
        $num++;
        $toadd .= "finishup.status = 'l_False'";
    }
    $toadd .= ")";

    $query = "
    select solverRun.runID as runID, tags.tag as fname, solverRun.gitrev as mygitrev
    from tags, solverRun left join finishup on (finishup.runID = solverRun.runID)
    where solverRun.runID = tags.runID
    and tags.tagname='filename'
    and $toadd
    order by tags.tag;";

    #print $query;

    $stmt = $sql->prepare($query);
    if (!$stmt) {
        print "Error:".$sql->lastErrorMsg();
        die("Cannot prepare statement");
    }
    $result = $stmt->execute();

    $numfiles = 0;
    while($arr=$result->fetchArray(SQLITE3_ASSOC))
    {
        $numfiles++;
        $data = array(
            'fname' => $arr["fname"],
            'runID' => $arr["runID"],
            'gitrev' => $arr["mygitrev"]
        );
        array_push($json, $data);
        # var_dump($arr);
    }
    $stmt->close();

    return $numfiles;
}

$numfiles = get_files_for_gitrev($sat, $unsat, $unfinished);

$ret = array(
    'filelist' => $json,
    'numfiles' => $numfiles
);
$jsonstring = json_encode($ret);
echo $jsonstring;
$sql->close();
?>
