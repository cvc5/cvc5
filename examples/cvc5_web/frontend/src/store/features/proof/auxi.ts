import { ClusterKind } from '../../../interfaces/enum';
import { NodeInterface, ProofState } from '../../../interfaces/interfaces';

interface ClusterColorMap {
    [type: number]: string;
}

function removeEscapedCharacters(s: string): string {
    let newS = '';
    for (let i = 0; i < s.length; i += 1) {
        if (
            !(
                s[i] === '\\' &&
                (s[i + 1] === '"' ||
                    s[i + 1] === '>' ||
                    s[i + 1] === '<' ||
                    s[i + 1] === '{' ||
                    s[i + 1] === '}' ||
                    s[i + 1] === '|')
            )
        ) {
            newS += s[i];
        }
    }

    return newS;
}

export function processDot(dot: string): [NodeInterface[], ProofState['letMap'], ClusterColorMap] {
    const nodes: NodeInterface[] = [
        {
            id: 0,
            conclusion: '',
            rule: '',
            args: '',
            children: [],
            parents: [NaN],
            descendants: 0,
            dependencies: [],
            clusterType: ClusterKind.NONE,
        },
    ];
    let comment: string | null = dot.slice(dot.indexOf('comment='));
    comment = comment
        ? removeEscapedCharacters(
              removeEscapedCharacters(comment.slice(comment.indexOf('=') + 2, comment.indexOf(';') - 1)),
          )
        : null;

    const clustersInfos: ClusterColorMap = {};
    const lines = dot
        .slice(dot.indexOf('{') + 1, dot.lastIndexOf('}') - 2)
        .replace(/(\n|\t)/gm, '')
        .split(';');
    lines.forEach((line) => {
        if (line.search('subgraph') !== -1) {
            // Get the label of this node subgraph
            let label = '';
            let idx = line.indexOf('label="') + 7;
            while (line[idx] !== '"') {
                label += line[idx];
                idx++;
            }

            // Get the label of this node subgraph
            let color = '';
            idx = line.indexOf('bgcolor="') + 9;
            while (line[idx] !== '"') {
                color += line[idx];
                idx++;
            }

            // Get the nodes ID's
            const numbers = line
                .substring(idx + 1, line.length - 1)
                .split(/\s/)
                .filter((str) => str.length)
                .map((num) => Number(num));

            let thisType: ClusterKind;
            switch (label) {
                case 'SAT':
                    thisType = ClusterKind.SAT;
                    break;
                case 'CNF':
                    thisType = ClusterKind.CNF;
                    break;
                case 'TL':
                    thisType = ClusterKind.TL;
                    break;
                case 'PP':
                    thisType = ClusterKind.PP;
                    break;
                case 'IN':
                    thisType = ClusterKind.IN;
                    break;
                default:
                    thisType = ClusterKind.NONE;
            }

            // Assign the type for each node
            numbers.forEach((num) => {
                nodes[num].clusterType = thisType;
            });
            clustersInfos[thisType] = color;
        } else if (line.search('label') !== -1) {
            const id = parseInt(line.slice(0, line.indexOf('[')).trim());
            const attributes = line.slice(line.indexOf('[') + 1, line.lastIndexOf(']')).trim();

            let label = attributes.slice(attributes.search(/[^\\]"/) + 3);
            label = label.slice(0, label.search(/[^\\]"/));
            let [conclusion, rule, args] = ['', '', ''];
            [conclusion, rule] = label.split(/\|/);
            [rule, args] = rule.indexOf(' :args ') != -1 ? rule.split(' :args ') : [rule, ''];

            const comment: string = removeEscapedCharacters(line.slice(line.indexOf('comment'), line.lastIndexOf('"')));
            const commentJSON = JSON.parse(comment.slice(comment.indexOf('"') + 1).replace(/'/g, '"'));

            if (!nodes[id]) {
                nodes[id] = {
                    id: id,
                    conclusion: '',
                    rule: '',
                    args: '',
                    children: [],
                    parents: [NaN],
                    descendants: 0,
                    dependencies: [],
                    clusterType: ClusterKind.NONE,
                };
            }
            nodes[id].conclusion = removeEscapedCharacters(conclusion);
            nodes[id].rule = removeEscapedCharacters(rule);
            nodes[id].args = removeEscapedCharacters(args);
            nodes[id].descendants = commentJSON.subProofQty;
        } else if (line.search('->') !== -1) {
            const [child, parent] = line.split('->').map((x) => parseInt(x.trim()));
            nodes[parent].children.push(child);
            // If there isn't a child node
            if (!nodes[child]) {
                nodes[child] = {
                    id: child,
                    conclusion: '',
                    rule: '',
                    args: '',
                    children: [],
                    parents: [],
                    descendants: 0,
                    dependencies: [],
                    clusterType: ClusterKind.NONE,
                };
            }
            // If there is and is an invalid parent
            else if (isNaN(nodes[child].parents[0])) {
                nodes[child].parents = [];
            }
            nodes[child].parents.push(parent);
        }
    });

    return comment ? [nodes, JSON.parse(comment)['letMap'], clustersInfos] : [nodes, {}, clustersInfos];
}

export const piNodeParents = (
    proof: NodeInterface[],
    hiddenNodesArray: number[],
    dependencies: { [parentId: number]: number[] } = {},
): number[] => {
    const parents = hiddenNodesArray
        // Concat all the parents
        .reduce((acc: number[], hiddenNode) => {
            let haveHiddenParent = false;

            proof[hiddenNode].parents.forEach((parent) => {
                // If this parent is a hidden node
                if (hiddenNodesArray.indexOf(parent) !== -1) {
                    haveHiddenParent = true;
                } else {
                    dependencies[parent]
                        ? dependencies[parent].push(hiddenNode)
                        : (dependencies[parent] = [hiddenNode]);
                }
            });

            if (haveHiddenParent) return acc;
            return acc.concat(proof[hiddenNode].parents);
        }, [])
        // Filter the duplicated elements
        .filter((parent, i, self) => self.indexOf(parent) === i)
        // Only the parents that aren't in he hidden nodes array remains
        .filter((parent) => hiddenNodesArray.indexOf(parent) === -1);

    // Removes the pi node parents from the dependencies
    Object.keys(dependencies).forEach((parent) => {
        const n = Number(parent);
        if (parents.indexOf(n) !== -1) delete dependencies[n];
    });

    return parents;
};

export const descendants = (proof: NodeInterface[], nodeId: number): number[] => {
    const validChildren = proof[nodeId].children.filter((node) => !proof[node].isHidden);
    return validChildren.concat(
        validChildren.reduce((acc: number[], childId) => {
            return acc.concat(descendants(proof, childId));
        }, []),
    );
};

export const piNodeChildren = (proof: NodeInterface[], hiddenNodesArray: number[]): number[] => {
    const children = hiddenNodesArray
        // Get all the childrens
        .reduce((acc: number[], hiddenNode) => acc.concat(proof[hiddenNode].children), [])
        // Exclude the childrens that are part of the hidden nodes
        .filter((child) => hiddenNodesArray.indexOf(child) === -1);
    return children;
};

export const findNodesClusters = (proof: NodeInterface[], hiddenNodesArray: number[]): number[][] => {
    const hiddenNodes = [...hiddenNodesArray];
    const clusters: number[][] = [];
    let clusteredNodes = 0;
    const parents = hiddenNodes.map((hiddenNode) => proof[hiddenNode].parents);

    // Cluster the nodes based on similiar parents
    parents.forEach((parent, clusterID) => {
        // If not all of the nodes where clustered and is a non empty cluster
        if (clusteredNodes !== parents.length && parents[clusterID].length) {
            clusters.push([]);
            parents.forEach((p, hiddenID) => {
                // If those nodes have some parent in commom and they weren't verified yet
                if (parents[hiddenID].length && parent.some((_p) => p.indexOf(_p) !== -1)) {
                    if (hiddenNodes[hiddenID]) clusters[clusters.length - 1].push(hiddenNodes[hiddenID]);
                    // Removes these parents from the array, making shure they will not get verified again (already clustered)
                    parents[hiddenID] = [];
                    // Increases the number o clustered nodes
                    clusteredNodes++;
                }
            });
        }
    });

    let pastCluster: number[][] = [];
    // Cluster the nodes until there aren't changes being made
    while (JSON.stringify(pastCluster) != JSON.stringify(clusters)) {
        pastCluster = [...clusters];
        clusters.forEach((cluster, clusterID) => {
            const clusterParents = proof[cluster[0]].parents;

            // For each cluster
            clusters.forEach((parentCluster, id) => {
                // If this parentCluster (cluster) is parent of the current cluster
                if (parentCluster.some((hiddenID) => clusterParents.indexOf(hiddenID) !== -1)) {
                    // Group the nodes couple in one single cluster (the parent cluster)
                    if (clusters[clusterID]) clusters[id] = clusters[id].concat(clusters[clusterID]);
                    clusters.splice(clusterID, 1);
                    clusterID--;
                }
            });
        });
    }

    // Filter the nodes with length 1
    return clusters.filter((cluster) => cluster.length > 1);
};

export const groupPiNodeDependencies = (
    proof: NodeInterface[],
    hiddenNodesArray: number[],
): NodeInterface['dependencies'] => {
    const piNodeDependencies: NodeInterface['dependencies'] = [];
    const depMap: { [piID: number]: number } = {};

    // Copy all the hidden nodes dependencies to the new pi node
    proof.forEach((node) => {
        // Search for all the hidden nodes that have deps
        if (hiddenNodesArray.indexOf(node.id) !== -1 && node.dependencies.length) {
            // For each dependence in this node
            node.dependencies.forEach((dep) => {
                // This pi node dependence wasn't inserted yet
                if (Object.keys(depMap).indexOf(String(dep.piId)) === -1) {
                    piNodeDependencies.push(dep);
                    depMap[dep.piId] = piNodeDependencies.length - 1;
                }
                // Concat the nodes inside the pi node already inserted
                else {
                    piNodeDependencies[depMap[dep.piId]].depsId = piNodeDependencies[depMap[dep.piId]].depsId.concat(
                        dep.depsId,
                    );
                }
            });
        }
    });
    return piNodeDependencies;
};

export const sliceNodesCluster = (
    proof: NodeInterface[],
    clusterMap: number[],
    nodeId = 0,
    slicedClusters: number[][] = [],
): number[][] => {
    const currentNode = proof[nodeId];

    // If the node id is valid and wasn't inserted yet
    if (nodeId && clusterMap[currentNode.id] === -1) {
        // Get all parents with the same type
        const parentsClusters: { [parentID: number]: number } = {};
        for (let i = 0; i < currentNode.parents.length; i++) {
            const p = currentNode.parents[i];
            if (proof[p].clusterType === currentNode.clusterType) {
                parentsClusters[p] = clusterMap[p];
                break;
            }
        }

        const keys = Object.keys(parentsClusters);

        // If the current node has the same type as (at least) one of it's parents
        if (keys.length) {
            // Put the current node in the cluster of the first parent with the same type
            const target = parentsClusters[Number(keys[0])];
            slicedClusters[target].push(currentNode.id);
            clusterMap[currentNode.id] = target;
        }
        // Parent with different type
        else {
            const clusterID = slicedClusters.length;
            clusterMap[currentNode.id] = clusterID;
            slicedClusters.push([currentNode.id]);

            // Add the brothers with the same type in the same cluster
            proof[currentNode.parents[0]].children.forEach((c) => {
                // If the brother node has the same type as the current one
                if (proof[c].clusterType === currentNode.clusterType && c !== currentNode.id) {
                    slicedClusters[clusterID].push(c);
                    clusterMap[c] = clusterID;
                }
            });
        }
    }

    currentNode.children.forEach((child) => {
        sliceNodesCluster(proof, clusterMap, child, slicedClusters);
    });
    return slicedClusters;
};

export const extractTheoryLemmas = (
    proof: NodeInterface[],
    clusters: ProofState['clustersInfos'],
    haveCluster: boolean,
): ProofState['theoryLemmaMap'] => {
    // If have clusters registered
    if (haveCluster) {
        return [proof[0].conclusion].concat(
            clusters.filter((c) => c.type === ClusterKind.TL).map((c) => proof[c.hiddenNodes[0]].conclusion),
        );
    } else {
        return proof.filter((n) => n.rule === 'SCOPE').map((n) => n.conclusion);
    }
};
