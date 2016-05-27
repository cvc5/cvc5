/*********************                                                        */
/*! \file antlr_line_buffered_input.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

// We rely on the inclusion of #include <antlr3.h> in
//   "parser/antlr_line_buffered_input.h".
// This is avoid having to undefine the symbols in <antlr3.h>.
// See the documentation in "parser/antlr_undefines.h" for more
// details.

#include "parser/antlr_line_buffered_input.h"

#include <iostream>
#include <string>
#include <cassert>

#include "base/output.h"

namespace CVC4 {
namespace parser {

static pANTLR3_INPUT_STREAM    antlr3CreateLineBufferedStream(std::istream& in);

static void
setupInputStream(pANTLR3_INPUT_STREAM input)
{
#if 0
    ANTLR3_BOOLEAN  isBigEndian;

    // Used to determine the endianness of the machine we are currently
    // running on.
    //
    ANTLR3_UINT16 bomTest = 0xFEFF;

    // What endianess is the machine we are running on? If the incoming
    // encoding endianess is the same as this machine's natural byte order
    // then we can use more efficient API calls.
    //
    if  (*((pANTLR3_UINT8)(&bomTest)) == 0xFE)
    {
        isBigEndian = ANTLR3_TRUE;
    }
    else
    {
        isBigEndian = ANTLR3_FALSE;
    }

    // What encoding did the user tell us {s}he thought it was? I am going
    // to get sick of the questions on antlr-interest, I know I am.
    //
    switch  (input->encoding)
    {
        case    ANTLR3_ENC_UTF8:

            // See if there is a BOM at the start of this UTF-8 sequence
            // and just eat it if there is. Windows .TXT files have this for instance
            // as it identifies UTF-8 even though it is of no consequence for byte order
            // as UTF-8 does not have a byte order.
            //
            if  (       (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0xEF
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0xBB
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+2))    == 0xBF
                )
            {
                // The UTF8 BOM is present so skip it
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 3);
            }

            // Install the UTF8 input routines
            //
            antlr3UTF8SetupStream(input);
            break;

        case    ANTLR3_ENC_UTF16:

            // See if there is a BOM at the start of the input. If not then
            // we assume that the byte order is the natural order of this
            // machine (or it is really UCS2). If there is a BOM we determine if the encoding
            // is the same as the natural order of this machine.
            //
            if  (       (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0xFE
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0xFF
                )
            {
                // BOM Present, indicates Big Endian
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 2);

                antlr3UTF16SetupStream(input, isBigEndian, ANTLR3_TRUE);
            }
            else if  (      (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0xFF
                        &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0xFE
                )
            {
                // BOM present, indicates Little Endian
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 2);

                antlr3UTF16SetupStream(input, isBigEndian, ANTLR3_FALSE);
            }
            else
            {
                // No BOM present, assume local computer byte order
                //
                antlr3UTF16SetupStream(input, isBigEndian, isBigEndian);
            }
            break;

        case    ANTLR3_ENC_UTF32:

            // See if there is a BOM at the start of the input. If not then
            // we assume that the byte order is the natural order of this
            // machine. If there is we determine if the encoding
            // is the same as the natural order of this machine.
            //
            if  (       (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0x00
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0x00
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+2))    == 0xFE
                    &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+3))    == 0xFF
                )
            {
                // BOM Present, indicates Big Endian
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 4);

                antlr3UTF32SetupStream(input, isBigEndian, ANTLR3_TRUE);
            }
            else if  (      (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar))      == 0xFF
                        &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0xFE
                        &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0x00
                        &&  (ANTLR3_UINT8)(*((pANTLR3_UINT8)input->nextChar+1))    == 0x00
                )
            {
                // BOM present, indicates Little Endian
                //
                input->nextChar = (void *)((pANTLR3_UINT8)input->nextChar + 4);

                antlr3UTF32SetupStream(input, isBigEndian, ANTLR3_FALSE);
            }
            else
            {
                // No BOM present, assume local computer byte order
                //
                antlr3UTF32SetupStream(input, isBigEndian, isBigEndian);
            }
            break;

        case    ANTLR3_ENC_UTF16BE:

            // Encoding is definately Big Endian with no BOM
            //
            antlr3UTF16SetupStream(input, isBigEndian, ANTLR3_TRUE);
            break;

        case    ANTLR3_ENC_UTF16LE:

            // Encoding is definately Little Endian with no BOM
            //
            antlr3UTF16SetupStream(input, isBigEndian, ANTLR3_FALSE);
            break;

        case    ANTLR3_ENC_UTF32BE:

            // Encoding is definately Big Endian with no BOM
            //
            antlr3UTF32SetupStream(input, isBigEndian, ANTLR3_TRUE);
            break;

        case    ANTLR3_ENC_UTF32LE:

            // Encoding is definately Little Endian with no BOM
            //
            antlr3UTF32SetupStream(input, isBigEndian, ANTLR3_FALSE);
            break;

        case    ANTLR3_ENC_EBCDIC:

            // EBCDIC is basically the same as ASCII but with an on the
            // fly translation to ASCII
            //
            antlr3EBCDICSetupStream(input);
            break;

        case    ANTLR3_ENC_8BIT:
        default:

            // Standard 8bit/ASCII
            //
            antlr38BitSetupStream(input);
            break;
    }
#endif /* 0 */
}

static ANTLR3_UCHAR
myLA(pANTLR3_INT_STREAM is, ANTLR3_INT32 la) {
    pANTLR3_INPUT_STREAM input;

    input   = ((pANTLR3_INPUT_STREAM) (is->super));

    Debug("pipe") << "LA" << std::endl;
    if	(( ((pANTLR3_UINT8)input->nextChar) + la - 1) >= (((pANTLR3_UINT8)input->data) + input->sizeBuf))
    {
      std::istream& in = *((CVC4::parser::pANTLR3_LINE_BUFFERED_INPUT_STREAM)input)->in;
      //MGD
      // in.clear();
      if(!in) {
        Debug("pipe") << "EOF" << std::endl;
        return	ANTLR3_CHARSTREAM_EOF;
      }
      Debug("pipe") << "READ" << std::endl;
      if(input->data == NULL) {
        Debug("pipe") << "ALLOC" << std::endl;
        input->data = malloc(1024);
        input->nextChar = input->data;
      } else {
        Debug("pipe") << "REALLOC" << std::endl;
        size_t pos = (char*)input->nextChar - (char*)input->data;
        input->data = realloc(input->data, input->sizeBuf + 1024);
        input->nextChar = (char*)input->data + pos;
      }
      in.getline((((char*)input->data) + input->sizeBuf), 1024);
      while(in.fail() && !in.eof()) {
        Debug("pipe") << "input string too long, reallocating" << std::endl;
        input->sizeBuf += strlen(((char*)input->data) + input->sizeBuf);
        size_t pos = (char*)input->nextChar - (char*)input->data;
        input->data = realloc(input->data, input->sizeBuf + 1024);
        input->nextChar = (char*)input->data + pos;
        in.clear();
        in.getline((((char*)input->data) + input->sizeBuf), 1024);
      }
      input->sizeBuf += strlen(((char*)input->data) + input->sizeBuf);
      assert(*(((char*)input->data) + input->sizeBuf) == '\0');
      Debug("pipe") << "SIZEBUF now " << input->sizeBuf << std::endl;
      *(((char*)input->data) + input->sizeBuf) = '\n';
      ++input->sizeBuf;
    }

    Debug("pipe") << "READ POINTER[" << la << "] AT: >>" << std::string(((char*)input->nextChar), input->sizeBuf - (((char*)input->nextChar) - (char*)input->data)) << "<< returning '" << (char)(*((pANTLR3_UINT8)input->nextChar + la - 1)) << "' (" << (unsigned)(*((pANTLR3_UINT8)input->nextChar + la - 1)) << ")" << std::endl;
    return	(ANTLR3_UCHAR)(*((pANTLR3_UINT8)input->nextChar + la - 1));
}


static void
myConsume(pANTLR3_INT_STREAM is)
{
    pANTLR3_INPUT_STREAM input;

    input   = ((pANTLR3_INPUT_STREAM) (is->super));

    Debug("pipe") << "consume! '" << *(char*)input->nextChar << "' (" << (unsigned)*(char*)input->nextChar << ")" << std::endl;
    if	((pANTLR3_UINT8)(input->nextChar) < (((pANTLR3_UINT8)input->data) + input->sizeBuf))
    {
	/* Indicate one more character in this line
	 */
	input->charPositionInLine++;

	if  ((ANTLR3_UCHAR)(*((pANTLR3_UINT8)input->nextChar)) == input->newlineChar)
	{
	    /* Reset for start of a new line of input
	     */
	    input->line++;
	    input->charPositionInLine	= 0;
	    input->currentLine		= (void *)(((pANTLR3_UINT8)input->nextChar) + 1);
            Debug("pipe") << "-- newline!" << std::endl;
	}

	/* Increment to next character position
	 */
	input->nextChar = (void *)(((pANTLR3_UINT8)input->nextChar) + 1);
        Debug("pipe") << "-- advance nextChar! looking at '" << *(char*)input->nextChar << "' (" << (unsigned)*(char*)input->nextChar << ")" << std::endl;
    } else Debug("pipe") << "-- nothing!" << std::endl;
}

pANTLR3_INPUT_STREAM
antlr3LineBufferedStreamNew(std::istream& in, ANTLR3_UINT32 encoding, pANTLR3_UINT8 name)
{
    pANTLR3_INPUT_STREAM    input;

    if(!in) {
      return NULL;
    }

    // First order of business is to set up the stream and install the data pointer.
    // Then we will work out the encoding and byte order and adjust the API functions that are installed for the
    // default 8Bit stream accordingly.
    //
    input   = antlr3CreateLineBufferedStream(in);
    if  (input == NULL)
    {
        return NULL;
    }

    // Size (in bytes) of the given 'string'
    //
    input->sizeBuf		= 0;

    input->istream->_LA		= myLA;
    input->istream->consume	= myConsume;

#ifndef CVC4_ANTLR3_OLD_INPUT_STREAM
    // We have the data in memory now so we can deal with it according to
    // the encoding scheme we were given by the user.
    //
    input->encoding = encoding;
#endif /* ! CVC4_ANTLR3_OLD_INPUT_STREAM */

    // Now we need to work out the endian type and install any
    // API functions that differ from 8Bit
    //
    setupInputStream(input);

    // Now we can set up the file name
    //
    input->istream->streamName	= input->strFactory->newStr8(input->strFactory, name);
    input->fileName		= input->istream->streamName;

    return input;
}

static pANTLR3_INPUT_STREAM
antlr3CreateLineBufferedStream(std::istream& in)
{
	// Pointer to the input stream we are going to create
	//
	pANTLR3_INPUT_STREAM    input;

	if	(!in)
	{
		return NULL;
	}

	// Allocate memory for the input stream structure
	//
	input   = (pANTLR3_INPUT_STREAM)
		ANTLR3_CALLOC(1, sizeof(ANTLR3_LINE_BUFFERED_INPUT_STREAM));

	if	(input == NULL)
	{
		return	NULL;
	}

	// Structure was allocated correctly, now we can install the pointer
	//
        input->data             = malloc(1024);
        input->isAllocated	= ANTLR3_FALSE;

        ((pANTLR3_LINE_BUFFERED_INPUT_STREAM)input)->in = &in;
	// Call the common 8 bit input stream handler
	// initialization.
	//
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
	antlr3AsciiSetupStream(input, ANTLR3_CHARSTREAM);
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
	antlr38BitSetupStream(input);
        // In some libantlr3c 3.4-beta versions, this call is not included in the above.
        // This is probably an erroneously-deleted line in the libantlr3c source since 3.2.
	antlr3GenericSetupStream(input);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */

        return  input;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
