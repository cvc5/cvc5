import { createSlice, PayloadAction } from '@reduxjs/toolkit';
import { RootState } from '../../store';
import { ExternalCmdState } from '../../../interfaces/interfaces';

const initialState: ExternalCmdState = {
    findData: {
        nodeToFind: -1,
        findOption: false,
    },
    renderData: {
        count: 0,
        fileChanged: false,
    },
    spinner: 'off',
    selectData: { type: false, square: { upperL: { x: -1, y: -1 }, lowerR: { x: -1, y: -1 } } },
};

export const externalCmd = createSlice({
    name: 'externalCmd',
    initialState,
    reducers: {
        findNode: (state, action: PayloadAction<{ nodeId: number; option: boolean }>) => {
            state.findData = { nodeToFind: action.payload.nodeId, findOption: action.payload.option };
        },
        reRender: (state) => {
            state.renderData.count = 0;
        },
        addRenderCount: (state) => {
            state.renderData.count++;
        },
        blockRender: (state) => {
            state.renderData.count = 2;
        },
        allowRenderNewFile: (state) => {
            state.renderData.fileChanged = true;
        },
        blockRenderNewFile: (state) => {
            state.renderData.fileChanged = false;
        },
        setSpinner: (state, action: PayloadAction<'off' | 'cvc5' | 'render'>) => {
            state.spinner = action.payload;
        },
        setSelectArea: (state, action: PayloadAction<ExternalCmdState['selectData']>) => {
            state.selectData = action.payload;
        },
    },
});

export const {
    findNode,
    reRender,
    addRenderCount,
    blockRender,
    allowRenderNewFile,
    blockRenderNewFile,
    setSpinner,
    setSelectArea,
} = externalCmd.actions;

export const selectFindData = (state: RootState): { nodeToFind: number; findOption: boolean } =>
    state.externalCmd.findData;

export const selectRenderData = (state: RootState): { count: number; fileChanged: boolean } =>
    state.externalCmd.renderData;

export const selectSpinner = (state: RootState): ExternalCmdState['spinner'] => state.externalCmd.spinner;

export const selectSelectData = (state: RootState): ExternalCmdState['selectData'] => state.externalCmd.selectData;

export default externalCmd.reducer;
