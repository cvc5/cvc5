import { configureStore, ThunkAction, Action } from '@reduxjs/toolkit';
import externalCmdReducer from './features/externalCmd/externalCmd';
import fileReducer from './features/file/fileSlice';
import proofReducer from './features/proof/proofSlice';
import themeReducer from './features/theme/themeSlice';

export const store = configureStore({
    reducer: {
        file: fileReducer,
        proof: proofReducer,
        theme: themeReducer,
        externalCmd: externalCmdReducer,
    },
});

export type AppDispatch = typeof store.dispatch;
export type RootState = ReturnType<typeof store.getState>;
export type AppThunk<ReturnType = void> = ThunkAction<ReturnType, RootState, unknown, Action<string>>;
