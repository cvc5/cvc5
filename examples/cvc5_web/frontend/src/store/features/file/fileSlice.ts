import { createSlice, PayloadAction } from '@reduxjs/toolkit';
import { RootState } from '../../store';
import { FileState } from '../../../interfaces/interfaces';

const initialState: FileState = {
    name: 'ex.smt2',
    value: 'digraph proof {\n\trankdir="BT";\n\tnode [shape=record];\n\t0 [label="{SCOPE((not a), a)|(not (and (not a) a))}", class = " basic ", comment = "{\'subProofQty\':1}" ];\n\t1 [label="{CHAIN_RESOLUTION(true, a)|false}", class = " propositional ", comment = "{\'subProofQty\':2}" ];\n\t2 [label="{ASSUME(a)|a}", comment = "{\'subProofQty\':0}"];\n\t3 [label="{ASSUME((not a))|(not a)}", comment = "{\'subProofQty\':0}"];\n\t1->0;\n\t2->1;\n\t3->1;\n}',
    filesCount: 0,
};

export const fileSlice = createSlice({
    name: 'file',
    initialState,
    // The `reducers` field lets us define reducers and generate associated actions
    reducers: {
        set: (state, action: PayloadAction<{ name: string; value: string }>) => {
            state.name = action.payload.name;
            if (state.value !== action.payload.value) {
                state.value = action.payload.value;
                state.filesCount++;
            }
        },
    },
});

export const { set } = fileSlice.actions;

// The function below is called a selector and allows us to select a value from
// the state. Selectors can also be defined inline where they're used instead of
// in the slice file. For example: `useSelector((state: RootState) => state.counter.value)`
export const selectFileName = (state: RootState): string => state.file.name;

export const selectFileExtension = (state: RootState): string => {
    const ext = state.file.name.split('.').pop();
    return ext ? ext : '';
};

export const selectDot = (state: RootState): string =>
    state.file.name.split('.').pop() === 'json' ? JSON.parse(state.file.value).dot : state.file.value;

export const selectFile = (state: RootState): string => state.file.value;

export const selectFileCount = (state: RootState): number => state.file.filesCount;

export default fileSlice.reducer;
