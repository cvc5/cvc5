import React, { useState } from 'react';

import { Intent, Position, Toaster } from '@blueprintjs/core';

import { useAppSelector } from '../../store/hooks';
import { selectTheme } from '../../store/features/theme/themeSlice';
import VisualizerSmtDrawer from '../VisualizerSmtDrawer/VisualizerSmtDrawer';

const App: React.FC = () => {
    const [smtDrawerIsOpen, setSmtDrawerIsOpen] = useState(true);
    const [smtOptions, setSmtOptions] = useState({ argsType: true, customArgs: '' });
    const darkTheme = useAppSelector(selectTheme);


    // Toaster
    let toaster: Toaster;
    const refHandlers = {
        toaster: (ref: Toaster) => (toaster = ref),
    };

    const addErrorToast = (err: string) => {
        toaster.show({ icon: 'warning-sign', intent: Intent.DANGER, message: err });
    };

    return (
        <div className={darkTheme ? ' bp3-dark' : ''} style={
            { 
                width: '100%', 
                height: '100%', 
                display: 'flex', 
                flex:'1', 
                justifyContent: 'center', 
                alignItems: 'center'
            }
        }>
            <Toaster position={Position.TOP} ref={refHandlers.toaster} />
            <VisualizerSmtDrawer
                isOpen={true}
                setDrawerIsOpen={setSmtDrawerIsOpen}
                addErrorToast={addErrorToast}
            />
        </div>
    );
};

export default App;
