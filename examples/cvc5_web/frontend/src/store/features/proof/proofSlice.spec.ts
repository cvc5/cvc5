import proofReducer, { ProofState, process, hideNodes, unhideNodes, applyView, changeStyle } from './proofSlice';

describe('proof reducer', () => {
    const initialState: ProofState = {
        proof: [],
        view: 'full',
        style: 'graph',
        hiddenNodes: [],
        letMap: {},
        visualInfo: [],
    };

    const proofExample: ProofState = {
        proof: [
            {
                id: 0,
                conclusion: 'SCOPE((not a), a)',
                rule: '(not (and (not a) a))',
                args: '',
                views: ['basic'],
                children: [1],
                parents: [NaN],
                descendants: 1,
            },
            {
                id: 1,
                conclusion: 'CHAIN_RESOLUTION(true, a)',
                rule: 'false',
                args: '',
                views: ['propositional'],
                children: [2, 3],
                parents: [0],
                descendants: 2,
            },
            {
                id: 2,
                conclusion: 'ASSUME(a)',
                rule: 'a',
                args: '',
                views: [''],
                children: [],
                parents: [1],
                descendants: 0,
            },
            {
                id: 3,
                conclusion: 'ASSUME((not a))',
                rule: '(not a)',
                args: '',
                views: [''],
                children: [],
                parents: [1],
                descendants: 0,
            },
        ],
        view: 'full',
        style: 'graph',
        hiddenNodes: [[2]],
        letMap: {},
        visualInfo: [],
    };

    it('should handle initial state', () => {
        expect(proofReducer(undefined, { type: 'unknown' })).toEqual({
            proof: [],
            view: 'full',
            style: 'graph',
            hiddenNodes: [],
        });
    });

    it('should handle process', () => {
        const actual = proofReducer(
            initialState,
            process(
                'digraph proof {\n\trankdir="BT";\n\tnode [shape=record];\n\t0 [label="{SCOPE((not a), a)|(not (and (not a) a))}", class = " basic ", comment = "{\'subProofQty\':1}" ];\n\t1 [label="{CHAIN_RESOLUTION(true, a)|false}", class = " propositional ", comment = "{\'subProofQty\':2}" ];\n\t2 [label="{ASSUME(a)|a}", comment = "{\'subProofQty\':0}"];\n\t3 [label="{ASSUME((not a))|(not a)}", comment = "{\'subProofQty\':0}"];\n\t1->0;\n\t2->1;\n\t3->1;\n}',
            ),
        );
        expect(actual.proof).toEqual(proofExample.proof);
    });

    it('should handle hide node', () => {
        const actual = proofReducer(proofExample, hideNodes([3]));
        expect(actual.hiddenNodes).toEqual([[2], [3]]);
    });

    it('should handle unhide node', () => {
        const actual = proofReducer(proofExample, unhideNodes([2]));
        expect(actual.hiddenNodes).toEqual([]);
    });

    it('should handle apply view - basic', () => {
        const actual = proofReducer(proofExample, applyView('basic'));
        expect(actual.view).toEqual('basic');
        expect(actual.hiddenNodes).toEqual([[1, 2, 3]]);
    });

    it('should handle apply view - propositional', () => {
        const actual = proofReducer(proofExample, applyView('propositional'));
        expect(actual.view).toEqual('propositional');
        expect(actual.hiddenNodes).toEqual([[2, 3]]);
    });

    it('should handle apply view - full', () => {
        const actual = proofReducer(proofExample, applyView('full'));
        expect(actual.view).toEqual('full');
        expect(actual.hiddenNodes).toEqual([]);
    });

    it('should handle change style - graph', () => {
        const actual = proofReducer(proofExample, changeStyle('graph'));
        expect(actual.style).toEqual('graph');
    });

    it('should handle change style - tree', () => {
        const actual = proofReducer(proofExample, changeStyle('directory'));
        expect(actual.style).toEqual('directory');
    });
});
