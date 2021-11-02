/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * IO manipulation classes.
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__IO_UTILS_H
#define CVC5__OPTIONS__IO_UTILS_H

#include <iosfwd>

#include "options/language.h"

namespace cvc5::options::ioutils
{
    void setDefaultDagThresh(int value);
    void setDefaultNodeDepth(int value);
    void setDefaultOutputLang(Language value);

    void applyDagThresh(std::ios_base& ios, int dagThresh);
    void applyNodeDepth(std::ios_base& ios, int nodeDepth);
    void applyOutputLang(std::ios_base& ios, Language outputLang);
    void apply(std::ios_base& ios, int dagThresh, int nodeDepth, Language outputLang);

    int getDagThresh(std::ios_base& ios);
    int getNodeDepth(std::ios_base& ios);
    Language getOutputLang(std::ios_base& ios);

    class Scope
    {
        public:
            Scope(std::ios_base& ios);
            ~Scope();
        private:
            std::ios_base& d_ios;
            int d_dagThresh;
            int d_nodeDepth;
            Language d_outputLang;
    };
}  // namespace cvc5::options::ioutils

#endif /* CVC5__OPTIONS__IO_UTILS_H */
