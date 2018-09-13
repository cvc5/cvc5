// Stores the original X sizes of the graphs
// used when zooming out fully

//for graphs
var origSizes = new Array();
var blockRedraw = false;
var graphs = new Array();

//For distibutions
var dists = [];

function setRollPeriod(num)
{
    for (var j = 0; j < graph_data.length; j++) {
        graphs[j].updateOptions( {
            rollPeriod: num
        } );
    }
}

//Draws all graphs using dygraphs
function drawAllGraphs()
{
    graphs = new Array();
    for (var i = 0; i < graph_data.length; i++) {
        console.log("printing graph "+i);
        graphs.push(drawOneGraph(i));
    }
}

//Draw one of the graphs
function drawOneGraph(i)
{
    console.log("putting to:");
    console.log(document.getElementById(graph_data[i].dataDivID));
    graph = new Dygraph(
        document.getElementById(graph_data[i].dataDivID),
        graph_data[i].data
        , {
            stackedGraph: graph_data[i].stacked,
            includeZero: graph_data[i].stacked,
            labels: graph_data[i].labels,
            //title: graph_data[i].title,
            underlayCallback: function(canvas, area, g) {
                canvas.fillStyle = "rgba(105, 105, 185, 185)";
                //Draw simplification points
                for(var k = 0; k < simplificationPoints.length-1; k++) {
                    var bottom_left = g.toDomCoords(simplificationPoints[k], -20);
                    var left = bottom_left[0];
                    canvas.fillRect(left, area.y, 2, area.h);
                }
            },
            axes: {
              x: {
                valueFormatter: function(d) {
                  return 'Conflict ' + d;
                },
                pixelsPerLabel: 100,
                includeZero: true,
                drawGrid: false,
                drawAxis: false,
              },
              y: {
                  drawGrid: false,
                  drawAxis: false,
              }
            },
            //stepPlot: true,
            //strokePattern: [0.1, 0, 0, 0.5],
            strokeWidth: 0.5,
            highlightCircleSize: 3,
            rollPeriod: (graph_data[i].tablename === "restart") ? 0: 0,
            legend: 'always',
            xlabel: false,
            labelsDiv: document.getElementById(graph_data[i].labelDivID),
            labelsSeparateLines: true,
            labelsKMB: true,
            drawPoints: true,
            pointSize: 1,
            strokeStyle: "black",
            errorBars: graph_data[i].minmax,
            customBars: graph_data[i].minmax,
            colors: (graph_data[i].simple_line ? ['#000000'] : ['#ef1414', '#efab14', '#1f3da2', '#1fad14', '#88109d', '#d0e913']),
            fillAlpha: (graph_data[i].minmax ? 0.1 : 0.5),
            dateWindow: [0, maxConflRestart],
            drawCallback: function(me, initial) {

                //Fill original sizes, so if we zoom out, we know where to zoom out
                if (initial)
                    origSizes = me.xAxisRange();

                //Initial draw, ignore
                if (blockRedraw || initial)
                    return;

                blockRedraw = true;
                var xrange = me.xAxisRange();

                //Zoom every one the same way
                for (var j = 0; j < graph_data.length; j++) {
                    //Don't go into loop
                    if (graphs[j] == me)
                        continue;

                    //If this is a full reset, then zoom out maximally
                    graphs[j].updateOptions( {
                        dateWindow: xrange
                    } );
                    //console.log(xrange);
                }

                blockRedraw = false;
            }
        }
    )

    return graph;
}

//Creates HTML for dygraphs
function createHTMLforGraphs()
{
    var datagraphs = document.getElementById("datagraphs");
    for (var i = 0; i < graph_data.length; i++) {
        datagraphs.innerHTML += '\
        <div id="' + graph_data[i].blockDivID + '">\
        <table id="plot-table-a">\
        <tr>\
        <td><div id="' + graph_data[i].dataDivID + '" class="myPlotData"></div></td>\
        <td id="labelW">\
            <table id="plot-table-a">\
                <tr><td>'+ graph_data[i].title +'</td></tr>\
                <tr><td><div id="' + graph_data[i].labelDivID + '" class="draghandle"></div></td></tr>\
            </table>\
        </td>\
        </tr>\
        </table>\
        </div>';
    }
}

function clear_everything()
{
    origSizes = new Array();
    blockRedraw = false;
    dists = [];

    datagraphs = document.getElementById("datagraphs");
    datagraphs.innerHTML = "";
}

function print_all_graphs()
{
    clear_everything();

    //Clear & create HTML
    createHTMLforGraphs();

    //Draws the graphs
    drawAllGraphs();
}

