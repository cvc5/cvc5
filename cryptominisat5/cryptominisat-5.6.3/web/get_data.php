<?php
include "connect.php";
$maxConfl = 50000000000;
//display_startup_errors(1);
//error_reporting(E_STRICT);

$runID = $_GET["id"];
# $runID = 5796126;

class MainDataGetter
{
    protected $numberingScheme;
    protected $data;
    protected $nrows;
    protected $colnum;
    protected $runID;
    protected $max_confl;
    protected $columndivs;
    protected $data_tmp;
    protected $tablename;
    protected $sql;
    protected $everyn;

    public function __construct($runID, $maxConfl)
    {
        global $sql;
        $this->runID = $runID;
        $this->numberingScheme = 0;
        $this->sql = $sql;
        $this->max_confl = $this->sql_get_max_restart($maxConfl);
        $this->columndivs = array();
        $this->data_tmp = array();
        $this->everyn = 200;
    }

    private function sql_get_max_restart($maxConfl)
    {

        $query="
        SELECT max(conflicts) as mymax FROM `restart`
        where conflicts < :conflicts
        and runID = :runID";

        $stmt = $this->sql->prepare($query);
        if (!$stmt) {
            die("Cannot prepare statement $query");
        }
        $stmt->bindValue(':conflicts', $maxConfl);
        $stmt->bindValue(':runID', $this->runID);
        $result = $stmt->execute();
        $dat = $result->fetchArray();
        $max = $dat["mymax"];
        $stmt->close();
        return $max;
    }

    public function get_max_confl()
    {
        return $this->max_confl;
    }

    protected function print_one_graph(
        $title
        , $datanames
        , $nicedatanames
        , $minmax = False
    ) {
        $json_data = array();

        //Start with an empty one
        $json_subarray = array();
        array_push($json_subarray, 0);
        $i = 0;
        while($i < sizeof($datanames)) {
            array_push($json_subarray, NULL);
            $i++;
        }
        array_push($json_data, $json_subarray);

        //Now go through it all
        $i=0;
        $last_confl_for_everyn = 0.0;
        $time_start = microtime();
        while ($i < $this->nrows) {
            $row = $this->data[$i];
            $confl = (int)$row["conflicts"];
            if ($confl -$last_confl_for_everyn < $this->everyn && $i < $this->nrows-1) {
                $i++;
                continue;
            }
            $last_confl_for_everyn = $confl;
            $json_subarray = array();
            array_push($json_subarray, $confl);

            //Calc local sum
            $local_sum = 0;
            foreach ($datanames as $dataname) {
                $local_sum += $row[$dataname];
            }

            //Print for each
            foreach ($datanames as $dataname) {
                $tmp = $row[$dataname];
                if (sizeof($datanames) > 1) {
                    if ($local_sum != 0) {
                        $tmp /= $local_sum;
                        $tmp *= 100.0;
                    }
                }

                if ($minmax) {
                    $tmp = array($row[$dataname."Min"], $tmp, $row[$dataname."Max"]);
                }
                array_push($json_subarray, $tmp);
            }
            array_push($json_data, $json_subarray);
            $i++;
        }
        $time = microtime() - $time_start;
        //echo "Took $time seconds\n";

        //Calculate labels
        $json_labels_tmp = array();
        array_push($json_labels_tmp, "Conflicts");
        foreach ($nicedatanames as $dataname) {
            array_push($json_labels_tmp, $dataname);
        }

        //Calculate blockDivID
        $blockDivID = "graphBlock".$this->numberingScheme;
        $fullname = "toplot_".$this->numberingScheme;

        //put into $this->data_tmp
        $json_data_tmp = array();
        $json_data_tmp['data'] = $json_data;
        $json_data_tmp['labels'] = $json_labels_tmp;
        $json_data_tmp['stacked'] = (int)(sizeof($datanames) > 1);
        $json_data_tmp['blockDivID'] = $blockDivID;
        $json_data_tmp['dataDivID'] = $fullname."_datadiv";
        $json_data_tmp['labelDivID'] = $fullname."_labeldiv";
        $json_data_tmp['max_confl'] = $this->max_confl;
        $json_data_tmp['title'] = $title;
        $json_data_tmp['minmax'] = $minmax;
        $json_data_tmp['tablename'] = $this->tablename;
        $json_data_tmp['simple_line'] = count($datanames) == 1;
        array_push($this->data_tmp, $json_data_tmp);

        //put into $this->columndivs
        $json_columndivs_tmp = array();
        $json_columndivs_tmp['blockDivID'] = $blockDivID;
        array_push($this->columndivs, $json_columndivs_tmp);

        $this->numberingScheme++;
    }

    function runQuery($table)
    {
        $this->tablename = $table;

        $query="
        SELECT *
        FROM `$table`
        where `runID` = :runID
        and conflicts <= :maxconfl
        order by `conflicts`";

        $stmt = $this->sql->prepare($query);
        if (!$stmt) {
            die("Cannot prepare statement $query");
        }
        $stmt->bindValue(":runID", $this->runID);
        $stmt->bindValue(":maxconfl", $this->max_confl);
        $result = $stmt->execute();

        $this->data = array();
        $this->nrows = 0;
        while($row = $result->fetchArray(SQLITE3_ASSOC) ) {
              array_push($this->data, $row);
              $this->nrows+=1;
       }
    }

    public function fill_data_tmp()
    {
        $this->runQuery("restart");

        $this->print_one_graph(
            "Time"
            , array("runtime")
            , array("")
            , False
        );

        $this->print_one_graph(
            "Distribution of clause types %"
            , array(
                "numIrredBins"
                , "numRedBins"
                , "numIrredLongs"
                , "numRedLongs"
            )
            ,array(
                "irred bin"
                , "red bin"
                , "irred long"
                , "ired long"
            )
        );

        $this->print_one_graph(
            "Avg. branch depth"
            , array("branchDepth")
            , array("")
            , False //set TRUE for standard deviation
        );

        $this->print_one_graph(
            "Avg. branch depth delta"
            , array("branchDepthDelta")
            , array("")
            , False //set TRUE for standard deviation
        );

        $this->print_one_graph(
            "Avg. trail depth"
            , array("trailDepth")
            , array("")
            , False //set TRUE for standard deviation
        );

        $this->print_one_graph(
            "Avg. trail depth delt"
            , array("trailDepthDelta")
            , array("")
            , False //set TRUE for standard deviation
        );

        $this->print_one_graph(
            "Avg. glue of newly learnt clauses"
            , array("glue")
            , array("")
            , False //set TRUE for standard deviation
        );

        $this->print_one_graph(
            "Avg. size of newly learnt clauses"
            , array("size")
            , array("")
            , False //set TRUE for standard deviation
        );

        $this->print_one_graph(
            "Avg. no. of resolutions carried out for 1st UIP"
            , array("resolutions")
            , array("")
            , False //set TRUE for standard deviation
        );

        $this->print_one_graph(
            "No. of variables replaced"
            , array("replaced")
            , array("")
        );

        $this->print_one_graph(
            "No. of variables\' values set"
            , array("set")
            , array("")
        );

        $this->print_one_graph(
            "Propagated polarity %"
            , array(
                "varSetPos"
                , "varSetNeg"
            )
            , array(
                "positive"
                , "negative")
        );

        $this->print_one_graph(
            "Newly learnt clause type %"
            , array(
            "learntUnits"
            , "learntBins"
            , "learntLongs"
            )
            ,array(
            "unit"
            , "binary"
            , "long")
        );

        $this->print_one_graph(
            "Propagation by %"
            , array(
            "propBinIrred", "propBinRed"
            , "propLongIrred", "propLongRed"
            )
            ,array("bin irred", "bin red"
            , "long irred", "long red"
            )
        );

        $this->print_one_graph(
            "Conflict caused by clause type %"
            , array(
            "conflBinIrred"
            , "conflBinRed"
            , "conflLongIrred"
            , "conflLongRed"
            )
            ,array(
            "bin irred"
            , "bin red"
            , "long irred"
            , "long red"
            )
        );

        /*print_one_graph("branchDepthSD", array("branchDepthSD")
            , array("branch depth std dev"));

        print_one_graph("branchDepthDeltaSD", array("branchDepthDeltaSD")
            , array("branch depth delta std dev"));

        print_one_graph("trailDepthSD", array("trailDepthSD")
            , array("trail depth std dev"));

        print_one_graph("trailDepthDeltaSD", array("trailDepthDeltaSD")
            , array("trail depth delta std dev"));

        print_one_graph("glueSD", array("glueSD")
            , array("newly learnt clause glue std dev"));

        print_one_graph("sizeSD", array("sizeSD")
            , array("newly learnt clause size std dev"));

        print_one_graph("resolutionsSD", array("resolutionsSD")
            , array("std dev no. resolutions for 1UIP"));*/

        $this->runQuery("reduceDB");

        return array($this->columndivs, $this->data_tmp, $this->numberingScheme);
    }
}


class Simplifications
{
    protected $runID;
    protected $sql;

    public function __construct($runID)
    {
        global $sql;
        $this->runID = $runID;
        $this->sql = $sql;
    }

    public function fillSimplificationPoints()
    {
        $query="
        SELECT max(conflicts) as confl, simplifications as simpl
        FROM restart
        where runID = :runID
        group by simplifications
        order by simplifications";

        $stmt = $this->sql->prepare($query);
        if (!$stmt) {
            die("Cannot prepare statement $query");
        }
        $stmt->bindValue(":runID", $this->runID);
        $result = $stmt->execute();

        $json_tmp = array();
        array_push($json_tmp, 0);
        while($arr=$result->fetchArray(SQLITE3_ASSOC))
        {
            $confl = (int)$arr["confl"];
            array_push($json_tmp, $confl);
        }
        return $json_tmp;
    }
}

function get_metadata($sql, $runID)
{
    $query="
    SELECT `startTime`
    FROM `startup`
    where runID = :runID";

    $stmt = $sql->prepare($query);
    if (!$stmt) {
        print "Error:".$sql->error;
        die("Cannot prepare statement $query");
    }
    $stmt->bindValue(":runID", $runID);
    $result = $stmt->execute();
    $dat = $result->fetchArray();
    $starttime = $dat["startTime"];
    $stmt->close();

    $query="
    SELECT `endTime`, `status`
    FROM `finishup`
    where runID = :runID";

    $stmt = $sql->prepare($query);
    if (!$stmt) {
        print "Error:".$sql->error;
        die("Cannot prepare statement $query");
    }
    $stmt->bindValue(":runID", $runID);
    $result = $stmt->execute();
    $dat = $result->fetchArray();
    $endTime = $dat["endTime"];
    $endTime = $dat["status"];
    $stmt->close();

    if ($ok) {
        $query="
        SELECT UNIX_TIMESTAMP(`endTime`)-UNIX_TIMESTAMP(`startTime`) as diffTime
        FROM `finishup`, `startup`
        where startup.runID = finishup.runID
        and startup.runID = :runID";

        $stmt = $sql->prepare($query);
        if (!$stmt) {
            print "Error:".$sql->error;
            die("Cannot prepare statement $query");
        }
        $stmt->bindValue(":runID", $runID);
        $result = $stmt->execute();
        $dat = $result->fetchArray();
        $difftime = $dat["diffTime"];
        $stmt->close();
    } else {
        $difftime = 0;
    }

    $json_ret = array();
    $json_ret["startTime"] = $starttime;
    $json_ret["endTime"] = $endtime;
    $json_ret["difftime"] = $difftime;
    $json_ret["status"] = $status;

    return $json_ret;
}

///Main Data
$main_data_getter = new MainDataGetter($runID, $maxConfl);
list($json_columndivs, $json_graph_data, $orderNum) = $main_data_getter->fill_data_tmp();
$json_maxconflrestart = $main_data_getter->get_max_confl();

///Simplification points
$simps = new Simplifications($runID);
$json_simplificationpoints = $simps->fillSimplificationPoints();

///Metadata
$metadata = get_metadata($sql, $runID);

$final_json = array();
$final_json["metadata"] = $metadata;
$final_json["columnDivs"] = $json_columndivs;
$final_json["graph_data"] = $json_graph_data;
$final_json["simplificationPoints"] = $json_simplificationpoints;
$final_json["maxConflRestart"] = $json_maxconflrestart;
$jsonstring = json_encode($final_json);
echo $jsonstring;
?>
