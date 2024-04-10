import counterReducer, { FileState, set } from './fileSlice';

describe('file reducer', () => {
    const initialState: FileState = {
        name: 'ex.smt2',
        value: 'digraph proof {\n\trankdir="BT";\n\tnode [shape=record];\n\t0 [label="{SCOPE((not a), a)|(not (and (not a) a))}", class = " basic ", comment = "{\'subProofQty\':1}" ];\n\t1 [label="{CHAIN_RESOLUTION(true, a)|false}", class = " propositional ", comment = "{\'subProofQty\':2}" ];\n\t2 [label="{ASSUME(a)|a}", comment = "{\'subProofQty\':0}"];\n\t3 [label="{ASSUME((not a))|(not a)}", comment = "{\'subProofQty\':0}"];\n\t1->0;\n\t2->1;\n\t3->1;\n}',
    };
    it('should handle initial state', () => {
        expect(counterReducer(undefined, { type: 'unknown' })).toEqual({
            name: 'ex.smt2',
            value: 'digraph proof {\n\trankdir="BT";\n\tnode [shape=record];\n\t0 [label="{SCOPE((not a), a)|(not (and (not a) a))}", class = " basic ", comment = "{\'subProofQty\':1}" ];\n\t1 [label="{CHAIN_RESOLUTION(true, a)|false}", class = " propositional ", comment = "{\'subProofQty\':2}" ];\n\t2 [label="{ASSUME(a)|a}", comment = "{\'subProofQty\':0}"];\n\t3 [label="{ASSUME((not a))|(not a)}", comment = "{\'subProofQty\':0}"];\n\t1->0;\n\t2->1;\n\t3->1;\n}',
        });
    });

    it('should handle set', () => {
        const actual = counterReducer(
            initialState,
            set({
                name: 'ex.smt2',
                value: 'digraph proof {\n\trankdir="BT";\n\tnode [shape=record];\n\t0 [label="{SCOPE((not a), a)|(not (and (not a) a))}", class = " basic ", comment = "{\'subProofQty\':1}" ];\n\t1 [label="{CHAIN_RESOLUTION(true, a)|false}", class = " propositional ", comment = "{\'subProofQty\':2}" ];\n\t2 [label="{ASSUME(a)|a}", comment = "{\'subProofQty\':0}"];\n\t3 [label="{ASSUME((not a))|(not a)}", comment = "{\'subProofQty\':0}"];\n\t1->0;\n\t2->1;\n\t3->1;\n}',
            }),
        );
        expect(actual).toEqual({
            name: 'ex.smt2',
            value: 'digraph proof {\n\trankdir="BT";\n\tnode [shape=record];\n\t0 [label="{SCOPE((not a), a)|(not (and (not a) a))}", class = " basic ", comment = "{\'subProofQty\':1}" ];\n\t1 [label="{CHAIN_RESOLUTION(true, a)|false}", class = " propositional ", comment = "{\'subProofQty\':2}" ];\n\t2 [label="{ASSUME(a)|a}", comment = "{\'subProofQty\':0}"];\n\t3 [label="{ASSUME((not a))|(not a)}", comment = "{\'subProofQty\':0}"];\n\t1->0;\n\t2->1;\n\t3->1;\n}',
        });
    });
});
