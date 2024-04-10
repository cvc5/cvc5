import { createSlice } from '@reduxjs/toolkit';
import { RootState } from '../../store';
import { ThemeState } from '../../../interfaces/interfaces';

const initialState: ThemeState = {
    value: true,
};

export const themeSlice = createSlice({
    name: 'theme',
    initialState,
    // The `reducers` field lets us define reducers and generate associated actions
    reducers: {
        toggle: (state) => {
            state.value = !state.value;
        },
    },
});

export const { toggle } = themeSlice.actions;

// The function below is called a selector and allows us to select a value from
// the state. Selectors can also be defined inline where they're used instead of
// in the slice theme. For example: `useSelector((state: RootState) => state.counter.value)`
export const selectTheme = (state: RootState): boolean => state.theme.value;

export default themeSlice.reducer;
