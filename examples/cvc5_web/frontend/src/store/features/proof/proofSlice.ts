import { createSlice } from '@reduxjs/toolkit';
import { RootState } from '../../store';
import { piNodeChildren, piNodeParents, groupPiNodeDependencies } from './auxi';
import { NodeInterface, ProofState } from '../../../interfaces/interfaces';
import { ClusterKind } from '../../../interfaces/enum';
import reducers from './reducers';

const initialState: ProofState = {
    proof: [],
    view: 'full',
    style: 'graph',
    hiddenNodes: [],
    letMap: {},
    theoryLemmaMap: [],
    visualInfo: {},
    nodesSelected: [],
    clustersInfos: [],
    smt: '',
};

export const proofSlice = createSlice({
    name: 'proof',
    initialState,
    reducers: reducers,
});

export const {
    process,
    hideNodes,
    foldAllDescendants,
    unfoldNodes,
    unfoldNextNode,
    setVisualInfo,
    selectByArea,
    unselectByArea,
    selectNodes,
    unselectNodes,
    changeStyle,
    applyView,
    applyColor,
    moveNode,
    setSmt,
    undo,
} = proofSlice.actions;

export const selectProof = (state: RootState): NodeInterface[] => {
    let proof = state.proof.proof;
    const hiddenNodes = state.proof.hiddenNodes;

    hiddenNodes.forEach((hiddenNodesArray) => {
        const dependencies: { [parentId: number]: number[] } = {};
        const children = piNodeChildren(proof, hiddenNodesArray);
        const parents = piNodeParents(proof, hiddenNodesArray, dependencies);
        const piNodeDependencies = groupPiNodeDependencies(proof, hiddenNodesArray);

        const piNodeId = proof.length;
        proof = proof.concat({
            id: piNodeId,
            conclusion: '∴',
            rule: 'π',
            args: '',
            children: children,
            parents: parents,
            hiddenNodes: hiddenNodesArray.map((hiddenNode) => proof[hiddenNode]),
            descendants: 1,
            dependencies: piNodeDependencies,
            clusterType: ClusterKind.NONE,
        });

        const piNode = proof[piNodeId];

        children.forEach(
            (childId) =>
                (proof[childId] = {
                    ...proof[childId],
                    parents: proof[childId].parents
                        .concat([piNodeId])
                        .filter((proofNode) => hiddenNodesArray.indexOf(proofNode) === -1),
                }),
        );
        parents.forEach(
            (parentId) =>
                (proof[parentId] = {
                    ...proof[parentId],
                    children: proof[parentId].children
                        .concat([piNodeId])
                        .filter((proofNode) => hiddenNodesArray.indexOf(proofNode) === -1),
                }),
        );

        // Set the dependencies array of each parent that has deps and remove
        //  the children that are dependencies
        Object.keys(dependencies).forEach((parent) => {
            const parentId = Number(parent);
            proof[parentId] = {
                ...proof[parentId],
                children: proof[parentId].children.filter((c) => dependencies[parentId].indexOf(c) === -1),
                dependencies: [...proof[parentId].dependencies, { piId: piNodeId, depsId: dependencies[parentId] }],
            };
        });

        // Get the high hierarchy nodes in this pi node
        const highHierarchyNodes = hiddenNodesArray?.filter((node) =>
            proof[node].parents.every((parentId) => piNode.parents.indexOf(parentId) !== -1),
        );

        // Get the conclusion array
        const conclusion = highHierarchyNodes.map((node) => ' ' + proof[node].conclusion);
        piNode.conclusion = conclusion.length > 1 ? `[${conclusion} ]` : `${conclusion}`;

        // Get the rule array
        const rule = highHierarchyNodes.map((node) => ' ' + proof[node].rule);
        piNode.rule = rule.length > 1 ? `[${rule} ]` : `${rule} `;

        // Set the descendants number
        piNode.descendants = piNode.children.reduce(
            (ac: number, childID) => ((ac += proof[childID].descendants), ac),
            1,
        );
    });

    proof = proof.filter((proofNode) =>
        hiddenNodes.every((hiddenNodesArray) => hiddenNodesArray.indexOf(proofNode.id) === -1),
    );

    return proof;
};

export const selectOriginalProof = (state: RootState): NodeInterface[] => {
    return state.proof.proof;
};

export const selectView = (state: RootState): ProofState['view'] => {
    return state.proof.view;
};

export const selectStyle = (state: RootState): 'graph' | 'directory' => {
    return state.proof.style;
};

export const selectLetMap = (state: RootState): { [Key: string]: string } => {
    return state.proof.letMap;
};

export const selectTheoryLemmas = (state: RootState): ProofState['theoryLemmaMap'] => {
    return state.proof.theoryLemmaMap;
};

export const selectVisualInfo = (state: RootState): ProofState['visualInfo'] => {
    if (state.proof.proof.length) return state.proof.visualInfo;
    // If there is no proof node
    return { 0: { color: '#555', x: 0, y: 0, selected: false } };
};

export const selectHiddenNodes = (state: RootState): number[][] => {
    return state.proof.hiddenNodes;
};

export const selectNodeClusters = (state: RootState): ProofState['clustersInfos'] => {
    return state.proof.clustersInfos;
};

export const selectSmt = (state: RootState): ProofState['smt'] => {
    return state.proof.smt;
};

export const selectNodesSelected = (state: RootState): ProofState['nodesSelected'] => {
    return state.proof.nodesSelected;
};

export default proofSlice.reducer;
