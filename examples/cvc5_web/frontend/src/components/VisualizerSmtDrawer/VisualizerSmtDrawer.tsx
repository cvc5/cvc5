import React, { useEffect, useReducer, useRef, useState } from 'react';

import MonacoEditor from '@monaco-editor/react';
import { Drawer, Position, Classes, Button} from '@blueprintjs/core';

import { selectTheme } from '../../store/features/theme/themeSlice';
import { SmtDrawerProps } from '../../interfaces/interfaces';
import { useAppDispatch, useAppSelector } from '../../store/hooks';

import { selectSmt, setSmt } from '../../store/features/proof/proofSlice';
import Module from '../../wasm/cvc5';
import { setSpinner } from '../../store/features/externalCmd/externalCmd';

import '../../scss/VisualizerSmtDrawer.scss';

const VisualizerSmtDrawer: React.FC<SmtDrawerProps> = ({
    isOpen,
    setDrawerIsOpen,
    addErrorToast,
}: SmtDrawerProps) => {
    const darkTheme = useAppSelector(selectTheme);
    const proofSmt = useAppSelector(selectSmt);

    const stdoutRef = useRef('');
    const stderrRef = useRef('');
    const changeOutRef = useRef(false);

    const [updateCounter, forceUpdate] = useReducer((x) => x + 1, 0);
    const [errorCounter, forceError] = useReducer((x) => x + 1, 0);
    const [optionsIsOpen, setOptionsIsOpen] = useReducer((open) => !open, false);
    const textRef = useRef(proofSmt + '\n');
    const [err, setErr] = useState('');

    // The default arguments used in the proof generation
    // good for testing --dump-proofs
    const defaultArgs = ['']
    const [currentOutput, setCurrentOutput] = useState('');
    const [inputFlags, setInputFlags] = useState('');

    const dispatch = useAppDispatch();

    useEffect(() => {
        textRef.current = proofSmt;
        forceUpdate();
    }, [proofSmt]);

    useEffect(() => {
        textRef.current = proofSmt;
        forceUpdate();
    }, [currentOutput]);

    useEffect(() => {
        if (errorCounter) addErrorToast(err);
    }, [errorCounter]);

    const options = {
        theme: darkTheme ? 'vs-dark' : 'vs',
        tabIndex: 5,
    };

    var on : "off" | "on" | "wordWrapColumn" | "bounded" = "on"
    var off : "off" | "on" | "wordWrapColumn" | "bounded" = "off"
    const outputOptions = {
        theme: darkTheme ? 'vs-dark' : 'vs',
        tabIndex: 5,
        readOnly: true,
        wordWrap: on,
        lineNumbers: off
    };

    const divColor = darkTheme ? 'rgb(255, 255, 255, 0.15)' : 'rgb(0, 0, 0, 0.15)';

    // Remove the cvc5> prompt message from the stdout
    const sanitizeDotResult = (result: string): string => result.replaceAll(/(cvc5> )+/g, '');
    const updateStdout = (str: string) => (stdoutRef.current += str + '\n');
    const updateStderr = (str: string) => (stderrRef.current += str + '\n');
    // Function called post the cvc5 execution
    const postCVC5run = (isThereError: boolean) => {
        // Sanitize the string
        setCurrentOutput(stdoutRef.current);
        stdoutRef.current = sanitizeDotResult(stdoutRef.current).trim();
        // If there was an error
        if (isThereError && !stdoutRef.current.length) {
            // Change the spin message to render
            dispatch(setSpinner('off'));

            setErr(
                stderrRef.current.length
                    ? stderrRef.current
                    : 'Error: Unknown error, check out the arguments parsed or the smt text.',
            );
            forceError();
        }
    };

    // Clean the output a single time during the cvc5 execution
    const cleanStdout = () => {
        if (!changeOutRef.current) {
            stdoutRef.current = '';
            changeOutRef.current = true;
        }
    };

    return (
        <Drawer
            className={`smt-drawer ${darkTheme ? 'bp3-dark' : ''}`}
            style={{ height: '100%', width: '75%', margin: 'auto' }}
            autoFocus={true}
            canEscapeKeyClose={true}
            canOutsideClickClose={false}
            enforceFocus={false}
            hasBackdrop={false}
            isOpen={isOpen}
            position={Position.TOP}
            usePortal={false}
            onClose={(e) => {
                e.preventDefault();
                setDrawerIsOpen(false);
                // Save the smt
                dispatch(setSmt(textRef.current));
            }}
            icon="code"
            title="cvc5 input"
        >
            <div className={Classes.DRAWER_BODY} style={{ overflow: 'hidden' }}>
                <MonacoEditor
                    height={'600px'}
                    language="graphql"
                    value={textRef.current}
                    onChange={(value) => value !== undefined && (textRef.current = value)}
                    onMount={() => forceUpdate()}
                    options={options}
                />
            </div>
            <div className={Classes.DRAWER_FOOTER}>
                <footer
                        style={{
                            position: 'relative',
                            borderTop: optionsIsOpen ? `solid 1px ${divColor}` : '',
                            display: 'flex',
                            alignItems: 'center'
                        }}
                >
                    <div className="bp3-input-group flags"
                        style={{
                            flex: '1',
                        }}
                    >
                        <span className="bp3-icon bp3-icon-filter"></span>
                        <input 
                            type="text"
                            className="bp3-input"
                            placeholder="Flags..."
                            onChange={(flags:React.ChangeEvent<HTMLInputElement>) => {setInputFlags(flags.target.value);}}
                        />
                        {/* {inputFlags} */}
                    </div>
                    <div style={{ float: 'right', display: 'flex' }}>
                        <Button
                            className="bp3-minimal margin-5"
                            icon="code"
                            text="Run cvc5"
                            onClick={async () => {
                                dispatch(setSmt(textRef.current));

                                let args = defaultArgs;
                                // If is default args
                                if (inputFlags) {
                                    args = inputFlags.split('--');
                                    args = args
                                        .map((arg) => arg.trim())
                                        .filter((arg) => {
                                            return arg.length !== 0;
                                        })
                                        .map((arg) => '--' + arg);
                                } else {
                                    args = [];
                                }

                                // Reset the stdout and stderr before executing cvc5
                                stdoutRef.current = '';
                                stderrRef.current = '';
                                changeOutRef.current = false;

                                // Only calls web assembly when there is some text on the code editor
                                if (textRef.current.trim().length) {
                                    dispatch(setSpinner('cvc5'));
                                    var inputTxt = textRef.current.replace(/(;(.)*|;(.)*\r\n|;(.)*\n|;(.)*\r|\r\n|\n|\r)/gm, "");
                                    const clausePattern = /^(\(check-sat\))+$/;
                                    const noClauses = inputTxt.replace(/\s+/g, '').match(clausePattern);
                                    // Run cvc5
                                    if (!noClauses)
                                    {
                                        Module({
                                            arguments: args,
                                            proofTxt: inputTxt,
                                            out: updateStdout,
                                            err: updateStderr,
                                            postCVC5: postCVC5run,
                                            cleanStdout: cleanStdout,
                                            binaryFileName: 'cvc5.wasm',
                                        })
                                        .then(()=>{
                                            setCurrentOutput(stdoutRef.current);
                                        });
                                    } else {
                                        setCurrentOutput("no clauses"); 
                                    }
                                }
                                // There isn't text in the code editor
                                else {
                                    addErrorToast('Error: Empty proof in the code editor.');
                                }
                            }}
                            tabIndex={3}
                        />
                    </div>
                </footer>
                </div>
                <MonacoEditor
                    height={'600px'}
                    language="graphql"
                    value={currentOutput}
                    onChange={(value) => value !== undefined && (textRef.current = value)}
                    onMount={() => forceUpdate()}
                    options={outputOptions}
                />
        </Drawer>
    );
};

export default VisualizerSmtDrawer;
