import React from 'react';
import ReactDOM from 'react-dom';
import App from './components/App/App';
import { store } from './store/store';
import { Provider } from 'react-redux';

import './scss/index.scss';

import reportWebVitals from './ReactUtils/reportWebVitals';

ReactDOM.render(
    <React.StrictMode>
        <Provider store={store}>
            <App />
        </Provider>
    </React.StrictMode>,
    document.getElementById('root'),
);

// If you want to start measuring performance in your app, pass a function
// to log results (for example: reportWebVitals(console.log))
// or send to an analytics endpoint. Learn more: https://bit.ly/CRA-vitals
reportWebVitals();
