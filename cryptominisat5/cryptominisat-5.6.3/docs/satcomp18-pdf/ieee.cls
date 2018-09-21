% Copyright 2014 IEEEE
% for terms of use see https://www.ieee.org/publications_standards/publications/rights/copyrightpolicy.html

% =========================================================================
% -------------------------------------------------------------------------
%               XX                              X
%                                               X
%               XX    XXX   XXX   XXX      XXX  X  XXXX
%                X   X   X X   X X   X    X   X X X
%                X   XXXXX XXXXX XXXXX    X     X  XXX
%                X   X     X     X     XX X   X X     X
%               XXX   XXX   XXX   XXX  XX  XXX  X XXXX
% -------------------------------------------------------------------------
% =========================================================================
% ieee.cls --- For formatting IEEE conference & journal papers
%          --- Compiled by Gregory Plett, Sept 1997
%
% This class was inspired by one first compiled by Gerry Murray and
% Silvano Balemi for LaTeX209. It was later updated for use with 
% LaTeX2e, and some bugs were fixed, all by Istvan Kollar. Lastly,
% I have tried to make the class easier to use by paper authors. 
% Significant new functionality has been added. Many routines are
% "borrowed" from other people's packages and modified extensively.
% When I rembered where I got the routines from, I gave the author
% credit.
% 
% After I made many changes on my own, I found a version by Peter
% N"uchter, and tried to retain some amount of compatibility with his
% version.  To be completely compatible with him, you may need to 
% manually:
% \usepackage{rawfonts}\usepackage{oldlfont}
% \AtBeginDocument{\parindent1.0em} (?)
%
%===========================================================================
%
% Usage:
%	\documentclass[main-mode,sub-mode,misc-options]{ieee}
%	\usepackage{your own packages}
%	\begin{document}
%	\bibliographystyle{IEEEbib}
%	\title[short]{regular}
%	\author[short]{full}
%	\maketitle
%	\begin{abstract}...\end{abstract}
%	\begin{keywords}...\end{keywords}
%	\section{...}
%	  \PARstart ... or \PARstartCal ...
%	...
%	\begin{biography}[picname.ps]{Author's name}...\end{biography}
%	\end{document}
%
% The document class options are:
%
% main-mode: One of the following is required. (draft is the default)
%	draft: Double-spaced, single column with date/time stamp.
%	submission: Double-spaced, suitable for submission for review.
%	compressed: Same as "submission", only single spaced.
%	final: Double-column, for assessing page-length and
%		format of final version.
%
% sub-mode:
%       techreport: This can modify "final" to produce a two-col
%               technical report.
%	internal: This can modify "submission", "compressed" or "final".
%		It changes the header to notify the reader that
%		this is a version of the manuscript to be used for
%		internal review processes only, and not to be
%		distributed.
%	submitted: This can modify "compressed" or "final". It changes
%		the header to notify the reader that this 
%		is a preprint and not to be distributed.
%	inpress: This can modify "compressed" or "final". It changes the
%		header to notify the reader that this paper has
%		been accepted for publishing, but it is not yet to be
%		distributed.
%	reprint: This can modify "final". It changes the header
%		to notify the reader where the paper is reprinted from.
%
% misc-options:
%	narroweqnarray: Changes the spacing around the "=" sign in 
%		equation arrays to make it the same as in displayed math.
%	inline: Compresses the horizontal spacing of inline math equations.
%       notitlepage: No separate title page. (default)
%       titlepage: Separate title page.
%       anonymous: Omit all author information from main part of paper.
%		Author info only prints on titlepage.
%       9pt,10pt,11pt,12pt: Choose the appropriate type size. You should 
%               not need to do this as the "correct" size is automatically
%               chosen. However, if you want, you may use these to change
%               the type size of the main text. "9pt" is a bit of a hack
%               to retain backward-compatibility.
%       invited: If the paper is an "invited" paper, then this option
%               prints "(Invited Paper)" under the authors' names.
%   
% For regular IEEE submissions, define the journal name as:
% \journal{IEEE Trans. Inst. Meas.}
% 
% To specify the conference place and date:
% \confplacedate{Ottawa, Canada, May 19--21, 1997}
% 
% Before \maketitle, define:
% \title{Title of paper}
% \author{Author1\member{Fellow}\authorinfo{Department of
% Electrical Engineering\\ Some University, Somewhere, CA 94305
% USA} \and Author2\member{Senior Member}\authorinfo{Deptartment of 
% Measurement and Instrument Eng., Another University, ...}}
% 
% Note, the contents of \authorinfo tends to vary depending on if it is
% a conference or journal paper. The amount of manual changes are
% small, and must be done by a human anyway. The example given is for an
% IMTC conference.
% 
% See also IEEEbib.bst and ieeefig.sty
% Also very useful for document preparation is the style file "endfloat",
% available on all CTAN TeX archives.
%
%===========================================================================
% modified 14 October 2002:
% 	- fixed bibliography listing of [#] when # < 10 and number of
%	  references is greater than 9. Thanks for Janos Markus for finding
%	  this bug and suggesting a solution.
% modified 15 January 2000:
%	- "fixed" narroweqnarray. Never implemented! Now it is...
% modified 12 January 2000:
%	- modified so only first \title and \author commands are recognized.
%	  This allows LyX to have \title and \author with full syntax in 
%         header, but dummy \title and \author show up in GUI.
%	- added "\date" so the \date command can change "submitted" and 
%         "draft" date headers. 
% modified 11 January 2000:
% 	- added PARstartLyX and PARstartCalLyX for LyX compatibility
% 	- added biographyLyX 
% modified 1 Dec 1997:
%       - fixed first page in reprint mode to be same length as other pages
%       - added "invited" misc-option
% modified 5 Sept 1997:
%	- added the inpress, reprint and internal sub-modes
%	- removed IMTC-conf and CDC-conf to separate files
% modified 1 Sept 1997:
%	- included Babel package compatibility
%	- removed paper title from header on first page of draft
%	  manuscript
%	- removed the fixed option "letterpaper" to allow a4paper (etc)
% modified 1 Aug 1997:
%	- included the CDC-conf option
%===========================================================================
% **************************************************************************
% ******                          ******************************************
% *****   LaTeX2e INITIALIZATION   *****************************************
% ******                          ******************************************
% **************************************************************************
\typeout{Document Class `ieee' <Modified: 2000, Gregory L. Plett>.}
\NeedsTeXFormat{LaTeX2e}[1993/11/11] % Oldest acceptable version of LaTeX2e
\ProvidesClass{ieee}[2000/01/11]     % Name of package provided, date
\def\i@@@cls{exists}

% Initial Code & Declaration of Options
% -------------------------------------
\newif\ifev@l \ev@lfalse             	% true if "final" mode.
\newif\ifsubm@t \subm@tfalse         	% true if "submission" mode.
\newif\ifdr@ft \dr@fttrue            	% true if "draft" mode.
\newif\ifc@mpress \c@mpressfalse       	% true if "compressed" mode.

\newif\if@technote \@technotefalse	% true if "technote" sub-mode.
\newif\ifintern@l  \intern@lfalse	% true if "internal" sub-mode.
\newif\ifprepr@nt \prepr@ntfalse	% true if "preprint" sub-mode.
\newif\ifinpr@ss \inpr@ssfalse		% true if "inpress" sub-mode.
\newif\ifrepr@nt \repr@ntfalse		% true if "reprint" sub-mode.

\newif\iftitlep@ge \titlep@gefalse     	% true if has own titlepage
\newif\if@non \@nonfalse		% true if anonymous
\newif\ifixpt \ixptfalse		% true if trying to do 9 pt
\newif\if@nvited \@nvitedfalse		% true if an invited paper

% Main options
% ------------
\DeclareOption{draft}{\ev@lfalse\subm@tfalse\dr@fttrue%
	\typeout{ieee: `Draft' mode selected.}}
\DeclareOption{submission}{\ev@lfalse\dr@ftfalse\subm@ttrue%
	\typeout{ieee: `Submission' mode selected.}}
\DeclareOption{compressed}{\ev@lfalse\dr@ftfalse\subm@tfalse\c@mpresstrue%
	\typeout{ieee: `Compressed' mode selected.}}
\DeclareOption{final}{\ev@ltrue\dr@ftfalse\subm@tfalse%
	\typeout{ieee: `Final' mode selected.}}
\DeclareOption{evaluation}{\ev@ltrue\dr@ftfalse\subm@tfalse%
	\typeout{ieee: `Final' mode selected.}} % synonym for final

% Sub options
% -----------
\DeclareOption{technote}{\@technotetrue%
	\typeout{ieee: `Technote' sub-mode selected.}}
\DeclareOption{internal}{\intern@ltrue\prepr@ntfalse\inpr@ssfalse\repr@ntfalse%
	\typeout{ieee: `Internal-Review' sub-mode selected.}}
\DeclareOption{submitted}{\intern@lfalse\prepr@nttrue\inpr@ssfalse\repr@ntfalse%
	\typeout{ieee: `Submitted' sub-mode selected.}}
\DeclareOption{preprint}{\intern@lfalse\prepr@nttrue\inpr@ssfalse\repr@ntfalse%
	\typeout{ieee: `Submitted' sub-mode selected.}} % synonym for submitted
\DeclareOption{inpress}{\intern@lfalse\prepr@ntfalse\inpr@sstrue\repr@ntfalse%
	\typeout{ieee: `Inpress' sub-mode selected.}}
\DeclareOption{reprint}{\intern@lfalse\prepr@ntfalse\inpr@ssfalse\repr@nttrue%
	\typeout{ieee: `Reprint' sub-mode selected.}}

% Misc options
% ------------
                                     	% regular or compressed "=" spacing in
\def\eqnarr@ysep{\arraycolsep}       	% eqnarray (this is the default)
                                     	% NOTE: we must use "def" and not "="
                                     	% as arraycolsep not yet defined.
\DeclareOption{narroweqnarray}{\gdef\eqnarr@ysep{0.28em\relax}%
	\typeout{ieee: Narrow equation arrays selected.}}
\DeclareOption{inline}{\everymath{\thinmuskip=2mu plus 1mu
        \medmuskip=3mu plus 1mu minus 2mu
        \thickmuskip=4mu plus 2mu\relax}%
	\typeout{ieee: Narrower inline equations selected.}}
\DeclareOption{notitlepage}{\titlep@gefalse%
	\typeout{ieee: No separate title page.}}
\DeclareOption{titlepage}{\titlep@getrue%
	\typeout{ieee: Use separate title page.}}
\DeclareOption{anonymous}{\@nontrue\AtBeginDocument{\glpexclude{biography}}
	\typeout{ieee: Omit author information from paper.}}
\DeclareOption{invited}{\@nvitedtrue%
	\typeout{ieee: (Invited Paper).}}

\DeclareOption{9pt}{\ixpttrue%
	\typeout{ieee: Trying to emulate old `9pt' document class.}}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}

% Execution of Options/Package Loading
% ------------------------------------
\newlength\narrowcol 
\newlength\parindentsave 		% recover parindent in blsone text

\ProcessOptions
\ifev@l			     	% if "final" mode...
  \if@technote\ixpttrue\typeout{ieee: Trying to emulate old `9pt' 
	document class.}\fi%
  \LoadClass[twoside,final,twocolumn,10pt]{article}
\else			     	% if "draft"/"submission"/(compressed) mode...
  \ifixpt
    \LoadClass[oneside,final,onecolumn,10pt]{article}
  \else
    \LoadClass[oneside,final,onecolumn,12pt]{article}
  \fi
\fi
\RequirePackage[final]{graphicx}
\RequirePackage{ifthen}

% Re-Definitions of English words which must be done before
% the Babel package (optional) is loaded.
% ---------------------------------------------------------
\def\keywordsname{Index Terms}
\def\indexterms#1{\def\keywordsname{#1}}
\def\appendicesname{Appendices}
\def\figurename{Fig.}

% **************************************************************************
% *****   Check Sub-Options for Compatibility w/ Main-Options   ************
% **************************************************************************
\if@technote\ifev@l\else\ClassError{ieee}{`technote' sub-mode may be
	used only with the `final' ^^Jmain-mode. It may not be used
	with either the `draft,' `submission,' or ^^J`compressed' 
	main-modes}{}\endinput\fi\fi
\ifintern@l\ifdr@ft\ClassError{ieee}{`internal' sub-mode may be
	used only with the ^^J`submission,' `compressed,' or `final' main-modes.
	It may not be used ^^Jwith the `draft' main-mode}{}\endinput\fi\fi
\ifprepr@nt\ifc@mpress\else\ifev@l\else\ClassError{ieee}{`submitted'
	sub-mode may be used only with the ^^J`compressed' or `final' 
	main-modes. It may not be used with either the ^^J`draft' or
	`submission' main-modes}{}\endinput\fi\fi\fi
\ifinpr@ss\ifc@mpress\else\ifev@l\else\ClassError{ieee}{`inpress'
	sub-mode may be used only with the `compressed' ^^Jor `final' 
	main-modes. It may not be used with either the `draft' or
	^^J`submission' main-modes}{}\endinput\fi\fi\fi
\ifrepr@nt\ifev@l\else\ClassError{ieee}{`reprint'
	sub-mode may be used only with the `final' ^^Jmain-mode. It may not be 
	used with either the `draft,' `submission,' or ^^J`compressed'
	main-modes}{}\endinput\fi\fi

% **************************************************************************
% *****   Page Layout Definition   *****************************************
% **************************************************************************
%% Layout definitions (mostly) common to all options.

\hoffset 0in 			\voffset 0in
\headheight        12pt 	\headsep            7mm
\marginparsep      10pt 	\marginparwidth    20pt
\marginparpush     25pt
\columnsep        4mm
\parindent        1.0em
\lineskip           1pt
\normallineskip     1pt
\def\baselinestretch{1}

\partopsep          \z@
\topsep           1.3ex
\parsep             \z@
\itemsep            \z@

\setlength{\parindentsave}{\parindent}

\ifev@l					% if "evaluation" mode
    % if camera-ready or A4paper ...
    \ifdim\paperwidth<211mm
      \oddsidemargin -11.4mm	\evensidemargin -11.4mm
    % for regular US Letter, not camera-ready
    \else
      \oddsidemargin -8.45mm	\evensidemargin -8.45mm
    \fi
    \ifrepr@nt
      \textheight 237.5mm		% leave 6mm for cpyright on first page
    \else
      \textheight 243.5mm		
    \fi
    \voffset -0.5in
    \textwidth 182.0mm
    \topmargin -12pt
    \setlength{\narrowcol}{89mm}
\else				     	% if "draft"/"submission" mode...
  \ifc@mpress				% and "compressed"
    \oddsidemargin -0.25in	\evensidemargin -0.25in
    \textheight 9in 		\textwidth 7in
    \topmargin -0.25in
    \setlength{\narrowcol}{7in}
  \else 				% and NOT "compressed"
    \renewcommand\baselinestretch{1.8}\renewcommand{\arraystretch}{0.8}
    \parindent=1.8\parindent
    \oddsidemargin 0pt 		\evensidemargin 0pt
    \headheight 12pt 		\headsep 0.375in
    \topmargin 0pt 		
    \textheight 8.5in 		\textwidth 6.5in
    \marginparsep 0in 		\marginparwidth 0pt
    \marginparpush 5pt
    \setlength{\narrowcol}{6.5in}
  \fi
\fi

\def\normalstyle{\rmfamily}

% **************************************************************************
% *****   Font Definition   ************************************************
% **************************************************************************
%% The 9-point option is being faked since it is not supported by the
%% article base class.

%% Check if we have selected 9 points
\ifixpt
\typeout{-- This is a 9 point document}
\gdef\@ptsize{9}
\def\@normalsize{\@setsize\normalsize{10.7pt}\ixpt\@ixpt
\abovedisplayskip 1em plus2pt minus5pt\belowdisplayskip \abovedisplayskip
\abovedisplayshortskip \z@ plus3pt\belowdisplayshortskip .6em plus3pt minus3pt
\topsep \belowdisplayshortskip%!PN
}
\def\small{\@setsize\small{9.12pt}\viiipt\@viipt}
\def\footnotesize{\@setsize\footnotesize{8.15pt}\viipt\@vipt}
\def\scriptsize{\@setsize\scriptsize{8pt}\vipt\@vpt}
\def\tiny{\@setsize\tiny{5pt}\vpt\@vpt}
\def\large{\@setsize\large{12pt}\xpt\@xpt}
\def\Large{\@setsize\Large{14pt}\xiipt\@xiipt}
\def\LARGE{\@setsize\LARGE{18pt}\xivpt\@xivpt}
\def\huge{\@setsize\huge{22pt}\xviipt\@xviipt}
\def\Huge{\@setsize\Huge{25pt}\xxpt\@xxpt}
\fi
%%
%% Check if we have selected 10 points
\def\@tempa{0}\if\@ptsize\@tempa
\typeout{-- This is a 10 point document}
\def\@normalsize{\@setsize\normalsize{11.9pt}\xpt\@xpt
\abovedisplayskip 1em plus2pt minus5pt\belowdisplayskip \abovedisplayskip
\abovedisplayshortskip \z@ plus3pt\belowdisplayshortskip .6em plus3pt minus3pt
\topsep \belowdisplayshortskip%!PN
}
\def\small{\@setsize\small{9.2pt}\viiipt\@viiipt}
\def\footnotesize{\@setsize\footnotesize{8.8pt}\viiipt\@viiipt}
\def\scriptsize{\@setsize\scriptsize{8pt}\viipt\@viipt}
\def\tiny{\@setsize\tiny{6pt}\vpt\@vpt}
\def\normalsize{\@setsize\normalsize{11.9pt}\xpt\@xpt}
\def\large{\@setsize\large{14pt}\xiipt\@xiipt}
\def\Large{\@setsize\Large{18pt}\xivpt\@xivpt}
\def\LARGE{\@setsize\LARGE{22pt}\xviipt\@xviipt}
\def\huge{\@setsize\huge{22pt}\xxpt\@xxpt}
\def\Huge{\@setsize\Huge{28pt}\xxvpt\@xxvpt}
\fi
%%
%% Check if we have selected 11 points
\def\@tempa{1}\if\@ptsize\@tempa
\typeout{-- This is an 11 point document}
\def\@normalsize{\@setsize\normalsize{13.6pt}\xipt\@xipt
\abovedisplayskip 1em plus2pt minus5pt\belowdisplayskip \abovedisplayskip
\abovedisplayshortskip \z@ plus3pt\belowdisplayshortskip .6em plus3pt minus3pt
\topsep \belowdisplayshortskip%!PN
}
\def\small{\@setsize\small{12pt}\xpt\@xpt}
\def\footnotesize{\@setsize\footnotesize{11pt}\ixpt\@ixpt}
\def\scriptsize{\@setsize\scriptsize{9.5pt}\viiipt\@viiipt}
\def\tiny{\@setsize\tiny{7pt}\vipt\@vipt}
\def\normalsize{\@setsize\normalsize{13.6pt}\xipt\@xipt}
\def\large{\@setsize\large{14pt}\xiipt\@xiipt}
\def\Large{\@setsize\Large{18pt}\xivpt\@xivpt}
\def\LARGE{\@setsize\LARGE{22pt}\xviipt\@xviipt}
\def\huge{\@setsize\huge{25pt}\xxpt\@xxpt}
\def\Huge{\@setsize\Huge{30pt}\xxvpt\@xxvpt}
\fi
%%
%% Check if we have selected 12 points
\def\@tempa{2}\if\@ptsize\@tempa
\typeout{-- This is a 12 point document}
\def\@normalsize{\@setsize\normalsize{14pt}\xiipt\@xiipt
\abovedisplayskip 1em plus3pt minus6pt\belowdisplayskip \abovedisplayskip
\abovedisplayshortskip \z@ plus3pt\belowdisplayshortskip .6em plus4pt minus4pt
\topsep \belowdisplayshortskip%!PN
}
\def\small{\@setsize\small{11.4pt}\xpt\@xpt}
\def\footnotesize{\@setsize\footnotesize{10pt}\ixpt\@ixpt}
\def\scriptsize{\@setsize\scriptsize{9pt}\viiipt\@viiipt}
\def\tiny{\@setsize\tiny{8pt}\vipt\@vipt}
\def\normalsize{\@setsize\normalsize{14pt}\xiipt\@xiipt}
\def\large{\@setsize\large{18pt}\xivpt\@xivpt}
\def\Large{\@setsize\Large{22pt}\xviipt\@xviipt}
\def\LARGE{\@setsize\LARGE{25pt}\xxpt\@xxpt}
\def\huge{\@setsize\huge{30pt}\xxvpt\@xxvpt}
\let\Huge=\huge
\fi

\AtBeginDocument{\normalsize\normalstyle\ps@headings\pagenumbering{arabic}}

% **************************************************************************
% *****   List Definition   ************************************************
% **************************************************************************
%% Change aspect of lists with
%% 1) \itemindent,  label indentation  wrt to left list margin
%% 2) \leftmargini, the indentation of the whole list (on left, first level)
\ifev@l
  \itemindent        -1em
  \leftmargini        2em
  \leftmarginii       1em
  \leftmarginiii    1.5em
  \leftmarginiv     1.5em
  \leftmarginv      1.0em
  \leftmarginvi     1.0em
\else
  \itemindent         -1em
  \leftmargini        3em
  \leftmarginii       3em
  \leftmarginiii      3em
  \leftmarginiv       3em
  \leftmarginv        3em
  \leftmarginvi       3em
\fi
%\itemindent        2em  % Alternative values: sometimes used..
%\leftmargini       0em
\labelsep           5pt
\leftmargin\leftmargini
\labelwidth         \z@

\def\@listI{\leftmargin\leftmargini} \@listI
\def\@listi{\leftmargin\leftmargini  \topsep \z@ plus 1pt minus 1pt}
\def\@listii{\leftmargin\leftmarginii\labelwidth\leftmarginii
    \advance\labelwidth-\labelsep    \topsep \z@}
\def\@listiii{\leftmargin\leftmarginiii\labelwidth\leftmarginiii
    \advance\labelwidth-\labelsep    \topsep \z@}
\def\@listiv{\leftmargin\leftmarginiv\labelwidth\leftmarginiv
    \advance\labelwidth-\labelsep    \topsep \z@}
\def\@listv{\leftmargin\leftmarginv\labelwidth\leftmarginv
    \advance\labelwidth-\labelsep    \topsep \z@}
\def\@listvi{\leftmargin\leftmarginvi\labelwidth\leftmarginvi
    \advance\labelwidth-\labelsep    \topsep \z@}

\def\labelenumi{\theenumi.}     \def\theenumi{\arabic{enumi}}
\def\labelenumii{(\theenumii)}  \def\theenumii{\alph{enumii}}
\def\labelenumiii{\theenumiii.} \def\theenumiii{\roman{enumiii}}
\def\labelenumiv{\theenumiv.}   \def\theenumiv{\Alph{enumiv}}
\def\p@enumii{\theenumi}
\def\p@enumiii{\theenumi(\theenumii)}
\def\p@enumiv{\p@enumiii\theenumiii}

\def\labelitemi{$\scriptstyle\bullet$}
\def\labelitemii{\bf --}
\def\labelitemiii{$\ast$}
\def\labelitemiv{$\cdot$}

%% \itemindent is set to \z@ by list, so define new temporary variable
\newdimen\tmpitemindent
\def\verse{\let\\=\@centercr
    \list{}{\itemsep\z@ \itemindent -1.5em \listparindent \itemindent
    \rightmargin\leftmargin\advance\leftmargin 1.5em}\item[]}
\let\endverse\endlist
\def\quotation{\list{}{\listparindent 1.5em \itemindent\listparindent
    \rightmargin\leftmargin \parsep 0pt plus 1pt}\item[]}
\let\endquotation=\endlist
\def\quote{\list{}{\rightmargin\leftmargin}\item[]}
\let\endquote=\endlist
\def\@mklab#1{#1}
\def\description{\tmpitemindent\itemindent\list{}{\itemindent\tmpitemindent
    \labelwidth\z@\def\makelabel##1{\hspace\labelsep\emph{##1}}}}
\def\enddescription{\endlist\par}
\def\enumerate{\tmpitemindent\itemindent\ifnum \@enumdepth >3 \@toodeep\else
    \advance\@enumdepth \@ne \edef\@enumctr{enum\romannumeral\the\@enumdepth}%
    \list{\csname label\@enumctr\endcsname}{\itemindent\tmpitemindent
    \usecounter{\@enumctr}\def\makelabel##1{\hspace\labelsep\hfil{##1}}}\fi}
\def\endenumerate{\endlist\par}
\def\itemize{\tmpitemindent\itemindent\ifnum \@itemdepth >3 \@toodeep\else
    \advance\@itemdepth\@ne
    \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
    \list{\csname\@itemitem\endcsname}{\itemindent\tmpitemindent
    \def\makelabel##1{\hspace\labelsep\hfil\emph{##1}}}\fi}
\def\enditemize{\endlist\par}

\newif\if@restonecol
\def\titlepage{\@restonecolfalse\if@twocolumn\@restonecoltrue\onecolumn
    \else \newpage \fi \thispagestyle{coverpagestyle}\c@page\z@}
\def\endtitlepage{\if@restonecol\twocolumn \else \newpage \fi%
\if@twoside\mbox{}\thispagestyle{coverpagestyle}\c@page\z@\cleardoublepage\fi}

\arraycolsep     5pt
\tabcolsep       6pt
\arrayrulewidth .4pt
\doublerulesep   2pt
\tabbingsep\labelsep

% **************************************************************************
% *****   Footnote Definition   ********************************************
% **************************************************************************
\skip\footins 10pt plus 5pt minus 2pt
\footnotesep 7pt 
\footskip 6mm
\skip\@mpfootins = \skip\footins
\fboxsep = 3pt \fboxrule = .4pt
\long\def\@makefntext#1{\parindent .8em\indent$^{\@thefnmark}$#1}
\def\footnoterule{}

% Reset baselinestretch within footnotes.
% Originally stolen from Stanford University thesis style.
% --------------------------------------------------------
\long\def\@footnotetext#1{\insert\footins{\blsone%
    \footnotesize\interlinepenalty\interfootnotelinepenalty
    \splittopskip\footnotesep
    \splitmaxdepth \dp\strutbox \floatingpenalty \@MM
    \hsize\columnwidth \@parboxrestore
    \edef\@currentlabel{\csname p@footnote\endcsname\@thefnmark}\@makefntext
    \let\par\\
    {\rule{\z@}{\footnotesep}\ignorespaces
      #1\strut}}}

% **************************************************************************
% *****   Keep track of Sections   *****************************************
% **************************************************************************
\if@technote
   \setcounter{secnumdepth}{3}
\else
   \setcounter{secnumdepth}{4}
\fi

\def\thesection{\@Roman\c@section}
\def\thesubsection{\Alph{subsection}}
\def\thesubsubsection{\thesubsection.\arabic{subsubsection}}
\def\thesubsubsectiondis{\Alph{subsection}.\arabic{subsubsection}}
\def\theparagraph{\thesubsubsection.\alph{paragraph}}
\def\theparagraphdis{\thesubsubsectiondis.\alph{paragraph}}

\def\theequation{\arabic{equation}}

% **************************************************************************
% *****   Table of Contents, List of Figures/Tables Definitions   **********
% **************************************************************************
\def\@pnumwidth{1.55em}
\def\@tocrmarg {2.55em}
\def\@dotsep{4.5}
\setcounter{tocdepth}{3}

\def\tableofcontents{\section*{\contentsname}\@starttoc{toc}}
\def\l@section#1#2{\addpenalty{\@secpenalty} \addvspace{1.0em plus 1pt}
    \@tempdima 1.8em \begingroup \parindent \z@ \rightskip \@pnumwidth
    \parfillskip-\@pnumwidth \bf\leavevmode #1\hfil\hbox to\@pnumwidth{\hss #2}
    \par \endgroup}
\def\l@subsection{\@dottedtocline{2}{1.5em}{2.3em}}
\def\l@subsubsection{\@dottedtocline{3}{3.8em}{3.2em}}
\def\listoffigures{\section*{\listfigurename}\@starttoc{lof}}
\def\l@figure{\@dottedtocline{1}{1em}{1.8em}}
\def\listoftables{\section*{\listtablename}\@starttoc{lot}}
\let\l@table\l@figure

% **************************************************************************
% *****   Float Definitions   **********************************************
% **************************************************************************
%% Normal Floats                      %% Double Column Floats
\floatsep 12pt plus 2pt minus 2pt     \dblfloatsep 12pt plus 2pt minus 2pt
\textfloatsep 20pt plus 2pt minus 4pt \dbltextfloatsep 20pt plus 2pt minus 4pt
%\@maxsep 20pt                         \@dblmaxsep 20pt %!PN
\@fptop 0pt plus 1fil                 \@dblfptop 0pt plus 1fil
\@fpsep 8pt plus 2fil                 \@dblfpsep 8pt plus 2fil
\@fpbot 0pt plus 1fil                 \@dblfpbot 0pt plus 1fil
\def\topfraction{1.0}                 \def\dbltopfraction{1.0}
\def\floatpagefraction{0.8}           \def\dblfloatpagefraction{0.8}
\setcounter{topnumber}{2}             \setcounter{dbltopnumber}{4}
%
\intextsep 12pt plus 2pt minus 2pt
\setcounter{bottomnumber}{2}
\def\bottomfraction{.4}
\setcounter{totalnumber}{4}
\def\textfraction{.2}

% Reset baselinestretch within floats.
% Originally stolen from Stanford University thesis style.
% --------------------------------------------------------
\def\@xfloat#1[#2]{\ifhmode \@bsphack\@floatpenalty -\@Mii\else
    \@floatpenalty-\@Miii\fi\def\@captype{#1}\ifinner
      \@parmoderr\@floatpenalty\z@
     \else\@next\@currbox\@freelist{\@tempcnta\csname ftype@#1\endcsname
       \multiply\@tempcnta\@xxxii\advance\@tempcnta\sixt@@n
       \@tfor \@tempa :=#2\do
                        {\if\@tempa h\advance\@tempcnta \@ne\fi
                         \if\@tempa t\advance\@tempcnta \tw@\fi
                         \if\@tempa b\advance\@tempcnta 4\relax\fi
                         \if\@tempa p\advance\@tempcnta 8\relax\fi
         }\global\count\@currbox\@tempcnta}\@fltovf\fi
    \global\setbox\@currbox\vbox\bgroup
    \def\baselinestretch{1}\small\normalsize
    \hsize\columnwidth \@parboxrestore}

% **************************************************************************
% *****   Caption Definition   *********************************************
% **************************************************************************
% some journals do not have centered captions for figures.
\newif\ifc@ptionleft \c@ptionlefttrue
\def\leftfigcaptions{\c@ptionlefttrue}
\def\centerfigcaptions{\c@ptionleftfalse}

\long\def\caption{\refstepcounter\@captype \@dblarg{\@caption\@captype}}

\long\def\@caption#1[#2]#3{\par\addcontentsline{\csname ext@#1\endcsname}{#1}{%
   \protect\numberline{\csname the#1\endcsname}{\ignorespaces #2}}
   \begingroup \@parboxrestore \normalsize
     \@makecaption{\csname fnum@#1\endcsname}{\ignorespaces #3}{#1}\par
   \endgroup}

\def\tablestring{table}
\def\figurestring{figure}

% changed by GLP to allow table captions to be set to a specific maximum
% width "\captionwidth", if defined.
\newlength{\captionindent}
\long\def\@makecaption#1#2#3{
\ifx\figurestring#3
    \vskip 5pt
    \setbox\@tempboxa\hbox{\small #1.~ #2}
    \ifdim \wd\@tempboxa >\hsize
       \setbox\@tempboxa\hbox{\small #1.~ }
       %\setlength\captionindent{\wd\@tempboxa} \divide\captionindent by 2
       %\parbox[t]{\hsize}{\small \hangindent \captionindent \hangafter=1%
       \parbox[t]{\hsize}{\small 
       \unhbox\@tempboxa#2}
    \else \hbox 
	to\hsize{\small\ifc@ptionleft\else\hfil\fi\box\@tempboxa\hfil}
    \fi
\else
  \begin{center}
  \ifx\captionwidth\undefined {\small #1}\\{\small\scshape #2}
  \else
    \begin{minipage}{\captionwidth}
    \begin{center}{\small #1}\\{\small\scshape #2}\end{center}
    \end{minipage}
  \fi
  \end{center}\vskip 4pt
\fi}

\def\thefigure{\@arabic\c@figure}
\def\fps@figure{tbp}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{\figurename\ \thefigure}
%\def\figure{\@float{figure}}		% GLP 
%\let\endfigure\end@float
\@namedef{figure*}{\@dblfloat{figure}}
\@namedef{endfigure*}{\end@dblfloat}

\def\thetable{\@Roman\c@table}
\def\fps@table{tbp}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{TABLE~\thetable}
\def\table{\@float{table}}
\let\endtable\end@float
\@namedef{table*}{\@dblfloat{table}}
\@namedef{endtable*}{\end@dblfloat}

% **************************************************************************
% *****   Header/Footer Definition   ***************************************
% **************************************************************************
% compute the time in hours and minutes; make new vars \timehh and \timemm
\newcount\timehh\newcount\timemm\timehh=\time\divide\timehh by 60
\timemm=\time\count255=\timehh\multiply\count255 by-60
\advance\timemm by \count255
\ifnum\timehh=12\def\apm{pm}\else
\ifnum\timehh>12\def\apm{pm}\advance\timehh by-12\else
\def\apm{am}\fi\fi
\def\t@me{\number\timehh\,:\,\ifnum\timemm<10 0\fi\number\timemm\,\apm}

% default definitions
% -------------------
\def\theevenhe@d{\footnotesize\thepage \hfil \leftmark\hbox{}}
\def\theoddhe@d{\hbox{}\footnotesize\rightmark \hfil \thepage}
\def\theevenf@@t{}
\def\theoddf@@t{}

\def\theeventphe@d{\footnotesize\thepage \hfil \hbox{}}
\def\theoddtphe@d{\hbox{}\footnotesize \hfil \thepage}
\def\theeventpf@@t{}
\def\theoddtpf@@t{}

\def\theevencphe@d{}
\def\theoddcphe@d{}
\def\theevencpf@@t{}
\def\theoddcpf@@t{}

\def\internalmsg{Preliminary version for evaluation: Please do not 
	circulate without the permission of the author(s)}
\def\submittedmsg{SUBMITTED FOR PUBLICATION TO:}
\def\acceptedmsg{ACCEPTED FOR PUBLICATION:}
\def\inpressmsg{(IN PRESS)}
\def\reprintmsg{REPRINTED FROM:}

% default cover page style (optional cover page)
% ----------------------------------------------
\def\ps@coverpagestyle{
  \def\@oddhead{\theoddcphe@d} \def\@evenhead{\theevencphe@d}
  \def\@oddfoot{\theoddcpf@@t} \def\@evenfoot{\theevencpf@@t}
}

% default title page style (first page of paper)
% ----------------------------------------------
\def\ps@titlepagestyle{
  \def\@oddhead{\theoddtphe@d} \def\@evenhead{\theeventphe@d}
  \def\@oddfoot{\theoddtpf@@t} \def\@evenfoot{\theeventpf@@t}
}

% default regular page style
% --------------------------
\if@twoside
  \def\ps@headings{
    \def\@oddhead{\theoddhe@d}
    \def\@evenhead{\theevenhe@d}
    \def\@oddfoot{\theoddf@@t} \def\@evenfoot{\theevenf@@t}
  }
\else
  \def\ps@headings{
    \def\@oddhead{\theoddhe@d}
    \def\@oddfoot{\theoddf@@t} 
    \def\@evenhead{} \def\@evenfoot{}
  }
\fi

% For draft mode (no sub-modes allowed)
% -------------------------------------
\ifdr@ft
  \def\leftmark{\sh@rttitle}\let\rightmark\leftmark
  \def\theoddf@@t{\footnotesize\today---\t@me\hfil DRAFT}
  \def\theevenf@@t{\footnotesize DRAFT\hfil\today---\t@me}
  \def\theoddtpf@@t{\footnotesize\today---\t@me\hfil DRAFT}
  \def\theeventpf@@t{\footnotesize DRAFT\hfil\today---\t@me}
\fi

% For submission mode (default plus internal sub-modes allowed)
% -------------------------------------------------------------
\ifsubm@t
  \def\leftmark{\sh@rttitle}\def\rightmark{\titl@line}
  \ifintern@l
    \def\theeventphe@d{\footnotesize\thepage \hfil \rightmark\hbox{}}
    \def\theoddtphe@d{\hbox{}\footnotesize\rightmark \hfil \thepage}
    \def\rightmark{\vbox to 0pt{\vss\hbox{\internalmsg} \hbox{\sh@rttitle}}}
    \def\leftmark{\vbox to 0pt{\vss\hbox{\internalmsg}
	\hbox{\phantom{\internalmsg}\llap{\sh@rttitle}}}}
  \else % put date on first page.
    \edef\TODAY{\uppercase{\today}}
    \def\theeventphe@d{\footnotesize\thepage \hfil \submittedmsg\ 
	\@journal\@titletext, \TODAY}
    \def\theoddtphe@d{\footnotesize\submittedmsg\ 
	\@journal\@titletext, \TODAY\hfil \thepage}
    \def\theevencphe@d{\footnotesize\hbox{} \hfil \submittedmsg\ 
	\@journal\@titletext, \TODAY}
    \def\theoddcphe@d{\footnotesize\submittedmsg\ 
	\@journal\@titletext, \TODAY\hfil \hbox{}}
  \fi
\fi

% For compressed mode (default, internal, submitted and  
% inpress sub-modes allowed)
% -----------------------------------------------------
\ifc@mpress
  \def\leftmark{\sh@rttitle}\def\rightmark{\titl@line}
  \ifintern@l
    \def\theeventphe@d{\footnotesize\thepage \hfil \rightmark\hbox{}}
    \def\theoddtphe@d{\hbox{}\footnotesize\rightmark \hfil \thepage}
    \def\rightmark{\vbox to 0pt{\vss\hbox{\internalmsg} \hbox{\sh@rttitle}}}
    \def\leftmark{\vbox to 0pt{\vss\hbox{\internalmsg}
	\hbox{\phantom{\internalmsg}\llap{\sh@rttitle}}}}
  \fi
  \ifprepr@nt
    \edef\TODAY{\uppercase{\today}}
    \def\theeventphe@d{\footnotesize\thepage \hfil \submittedmsg\ 
	\@journal\@titletext, \TODAY}
    \def\theoddtphe@d{\footnotesize\submittedmsg\ 
	\@journal\@titletext, \TODAY\hfil \thepage}
    \def\theevencphe@d{\footnotesize\hbox{} \hfil \submittedmsg\ 
	\@journal\@titletext, \TODAY}
    \def\theoddcphe@d{\footnotesize\submittedmsg\ 
	\@journal\@titletext, \TODAY\hfil \hbox{}}
  \fi
  \ifinpr@ss
    \def\leftmark{\acceptedmsg\ \@journal\@titletext, \inpressmsg}
    \def\theeventphe@d{\footnotesize\thepage \hfil \leftmark\hbox{}}
    \def\theoddtphe@d{\hbox{}\footnotesize\leftmark \hfil \thepage}
  \fi
\fi

% For final (evaluate) mode (default, techreport, internal, 
% submitted, inpress and reprint sub-modes allowed)
% ---------------------------------------------------------
\ifev@l
  \edef\TODAY{\uppercase{\today}}
  \def\leftmark{\@journal\@titletext}\def\rightmark{\titl@line}
  \def\theeventphe@d{\footnotesize\thepage \hfil \leftmark\hbox{}}
  \def\theoddtphe@d{\hbox{}\footnotesize\leftmark \hfil \thepage}
  \if@technote % make header a little bigger
    \def\theevenhe@d{\small\thepage \hfil \leftmark\hbox{}}
    \def\theoddhe@d{\hbox{}\small\rightmark \hfil \thepage}
    \def\theeventphe@d{\small\thepage \hfil \leftmark\hbox{}}
    \def\theoddtphe@d{\hbox{}\small\leftmark \hfil \thepage}
  \fi
  \ifintern@l
    \def\theeventphe@d{\footnotesize\thepage \hfil \rightmark\hbox{}}
    \def\theoddtphe@d{\hbox{}\footnotesize\rightmark \hfil \thepage}
    \def\rightmark{\vbox to 0pt{\vss\hbox{\internalmsg} \hbox{\sh@rttitle}}}
    \def\leftmark{\vbox to 0pt{\vss\hbox{\internalmsg}
	\hbox{\phantom{\internalmsg}\llap{\sh@rttitle}}}}
  \fi
  \ifprepr@nt
    \def\leftmark{\submittedmsg\ \@journal\@titletext, \TODAY}
  \fi
  \ifinpr@ss
    \def\leftmark{\acceptedmsg\ \@journal\@titletext, \inpressmsg}
  \fi
  \ifrepr@nt
    % reset page size on second and following pages b/c no copyright info
    \let\oldshipout\shipout
    \gdef\shipout{\global\textheight 243.5mm\oldshipout}
    \def\theeventpf@@t{\footnotesize\hfil\@ieeecopyright\hfil}
    \def\theoddtpf@@t{\footnotesize\hfil\@ieeecopyright\hfil}
    \def\leftmark{\reprintmsg\ \@journal\@titletext}
  \fi
\fi

%% Defines the command for putting the header. footernote{TEXT} is the same
%% as markboth{TEXT}{TEXT}. Here for compatibility with other style files.
\def\markboth#1#2{\def\leftmark{#1}\def\rightmark{#2}}
\def\footernote#1{\markboth{#1}{#1}}

% **************************************************************************
% *****   Citation/Bibliography Definitions   ******************************
% **************************************************************************
%% separate citations with "], ["
\def\@citex[#1]#2{\if@filesw\immediate\write\@auxout{\string\citation{#2}}\fi
\def\@citea{}\@cite{\@for\@citeb:=#2\do {\@citea\def\@citea{],
[}\@ifundefined {b@\@citeb}{{\bf ?}\@warning {Citation `\@citeb' on
page \thepage \space undefined}}%
{\csname b@\@citeb\endcsname}}}{#1}}

\def\@cite#1#2{[{#1\if@tempswa, #2\fi}]}

%% Allow short (name-less) citations, when used in conjunction with a
%% bibliography style that creates labels like \citename{<names>, }<year>
\let\@internalcite\cite
\def\cite{\def\citename##1{##1}\@internalcite}
\def\shortcite{\def\citename##1{}\@internalcite}
\def\@biblabel#1{\def\citename##1{##1}[#1]\hfill}

\def\thebibliography#1{\section*{\refname}\footnotesize\list
    {\hss[\arabic{enumi}]}{\settowidth\labelwidth{[#1]}\leftmargin\labelwidth
    \advance\leftmargin\labelsep \itemsep 0pt plus .5pt
    \usecounter{enumi}}
    \def\newblock{\hskip .11em plus .33em minus .07em}
    \sloppy\clubpenalty4000\widowpenalty4000
    \sfcode`\.=1000\relax
    \ifev@l\else\normalsize\fi %added by GLP
}
\let\endthebibliography=\endlist

% **************************************************************************
% *****   Appendix/Appendices Definitions   ********************************
% **************************************************************************
\newcounter{numappendices}\setcounter{numappendices}{0}
\newif\ifappendix \appendixfalse
%% appendix command for one single appendix
\def\appendix{\par
    \appendixtrue
    \typeout{appendices: \arabic{numappendices}}
    \setcounter{section}{0}\setcounter{subsection}{0}
    \gdef\thesection{\Alph{section}} 
    \ifnum \value{numappendices}>1 
       \section*{\appendicesname}
    \else
       \section*{\appendixname}
    \fi
    \setcounter{numappendices}{0}
}
%% appendices command for multiple appendicies
\def\appendices{\par
    \appendixtrue
    \typeout{appendices: \arabic{numappendices}}
    \setcounter{section}{0}\setcounter{subsection}{0}
    \gdef\thesection{\Alph{section}} \section*{\appendicesname}
    \setcounter{numappendices}{0}
}
\AtEndDocument{\if@filesw\immediate\write\@auxout{\string\setcounter{numappendices}{\arabic{numappendices}}}\fi}

% **************************************************************************
% *****   Title Definitions   **********************************************
% **************************************************************************
\def\titl@line{\sh@rttitle}	%for the header at the top of the page.

\def\@title{\typeout{ieee: Warning! No \noexpand\title given!}}
\def\title{\@ifnextchar [{\titlea}{\titleb}}%]

\def\set@title#1{\gdef\@title{#1}\global\def\set@title##1{}}
\def\setsh@rttitle#1{\gdef\sh@rttitle{#1}\global\def\setsh@rttitle##1{}}
\def\titlea[#1]#2{\set@title{#2}\setsh@rttitle{\uppercase{#1}}}
\def\titleb#1{\set@title{#1}\setsh@rttitle{\uppercase{#1}}}

\def\authorinfo#1{\let\\\relax\thanks{#1}}

\ifev@l
  \if@technote
    \def\member#1{}
  \else
    \def\member#1{, \emph{#1, IEEE}}
  \fi
\else
  \def\member#1{}
\fi 

\def\and{\unskip%                  % \begin{tabular}
\end{tabular}%
\hskip 0pt plus 0.1pt%
\begin{tabular}[t]{@{}c@{}}\ }%

\def\@author{\typeout{ieee: Warning! No \noexpand\author given!}}
\def\author{\@ifnextchar [{\authora}{\authorb}}%]
\def\set@author#1{\gdef\@author{#1}\global\def\set@author##1{}}
\def\settitl@line#1{\gdef\titl@line{#1}\global\def\settitl@line##1{}}
\def\authora[#1]#2{\set@author{#2}\if@non\else\settitl@line{#1: \sh@rttitle}\fi}
\def\authorb#1{\set@author{#1}}

\def\date#1{\def\today{#1}\edef\TODAY{\uppercase{\today}}}

\long\def\maketitle{%
  \begingroup
    \let\@thanks\@empty
    \renewcommand\thefootnote{} % the \thanks{} mark type is empty
    \iftitlep@ge\begin{titlepage}\@maketitlepage\@thanks\end{titlepage}%
	\let\@thanks\@empty\fi
    \thispagestyle{titlepagestyle}
    \if@twocolumn
      \if@technote
         %\if@twoside\newpage\cleardoublepage\else\newpage\fi%
         \newpage\global\@topnum\z@
         \ifrepr@nt
           \ifx\@loginfo\undefined\typeout{ieee: Warning! No \noexpand\loginfo 
           given!}\else\let\\\relax\thanks{\@loginfo}\fi%
         \fi
         \@maketitle
      \else
        \ifnum \col@number=\@ne 
          \ifrepr@nt
            \ifx\@loginfo\undefined\typeout{ieee: Warning! No \noexpand\loginfo 
	    given!}\else\let\\\relax\thanks{\@loginfo}\fi%
         \fi
         \@maketitle
        \else \twocolumn[%
          \ifrepr@nt%
            \ifx\@loginfo\undefined\typeout{ieee: Warning! No \noexpand\loginfo%
	    given!}\else\let\\\relax\thanks{\@loginfo}\fi%
         \fi%
         \@maketitle]%
        \fi
      \fi
    \else
      \newpage
      \global\@topnum\z@   % Prevents figures from going at top of page.
      \ifrepr@nt 
        \ifx\@loginfo\undefined\typeout{ieee: Warning! No \noexpand\loginfo 
        given!}\else\let\\\relax\thanks{\@loginfo}\fi
      \fi
      \@maketitle
    \fi
    \thispagestyle{titlepagestyle}%
    \@thanks
  \endgroup
  \setcounter{footnote}{0}%
  \global\let\thanks\relax \global\let\maketitle\relax
  \global\let\@maketitle\relax \global\let\@thanks\@empty
  \global\let\@author\@empty \global\let\@date\@empty
  \global\let\@title\@empty \global\let\title\relax
  \global\let\author\relax \global\let\date\relax
  \global\let\and\relax
}

\long\def\@maketitle{\unskip\newpage%
    \begin{center}\blsone
    \let \footnote \thanks
    \if@technote
      {\bfseries\@title\par}\if@non\else\vskip 1.3em{\lineskip .5em
	\noindent\begin{tabular}[t]{@{}c@{}}\@author\end{tabular}}\fi\par
    \else\unskip
      \noindent{\Huge\@title\par}%
      \if@non\else\vskip1.0em%
        \noindent{\large\lineskip .5em%
        \begin{tabular}[t]{@{}c@{}}\@author\end{tabular}}%
      \fi\par%
      \if@nvited\vskip1.0em\noindent\emph{\large(Invited Paper)}\par\fi
    \fi
    \ifrepr@nt
      \ifx\@lognumber\undefined\typeout{ieee: Warning! No 
      \noexpand\pubitemident or \noexpand\lognumber 
      given!}\else\thanks{\@lognumber}\fi%
    \fi
    \end{center}\par\vskip 0.5em}%

\long\def\@maketitlepage{\newpage%
    \mbox{}\vfil
    \begin{center}\blsone
    \let \footnote \thanks
    \if@technote
      {\bfseries\@title\par}\vskip 1.3em{\lineskip .5em
        \noindent\begin{tabular}[t]{@{}c@{}}\@author\end{tabular}\par}
    \else
      \vskip0.2em{\Huge\@title\par}\vskip1.0em%
      \iftitlep@ge\vfil\fi
      \noindent{\large\lineskip .5em%
      \begin{tabular}[t]{@{}c@{}}\@author\end{tabular}\par}%
    \fi
    \end{center}\par\vfil\mbox{}}

\def\@journal{\typeout{ieee: Warning! No \noexpand\journal given!}}
\def\journal#1{\def\@journal{\uppercase{#1}}}

\def\@ieeecopyright{\typeout{ieee: Warning! No \noexpand\ieeecopyright given!}}
\def\ieeecopyright#1{\def\@ieeecopyright{#1}}

\def\lognumber#1{\def\@lognumber{IEEE Log Number #1.}}
\def\pubitemident#1{\def\@lognumber{Publisher Item Identifier #1.}}
\long\def\loginfo#1{\long\def\@loginfo{\hbox{\vrule height 3ex width \z@}#1}}

\def\sh@rttitle{}
\def\@titletext{}
\def\titletext#1{\def\@titletext{#1}}

\def\firstpage#1{\setcounter{page}{#1}}

% **************************************************************************
% *****   Abstract Definition   ********************************************
% **************************************************************************
\def\abstract{%
  \if@twocolumn
    \small\bfseries{\itshape\abstractname\/---}%
  \else
    \begin{center}\vspace{-0.8em}\small\bf\abstractname\end{center}
    \quotation\small
  \fi\ignorespaces}
\def\endabstract{\vspace{0.6em}\par\if@twocolumn\else\endquotation\fi
  \normalsize\normalstyle}

% **************************************************************************
% *****   Keywords Definition   ********************************************
% **************************************************************************
\def\keywords{\vspace{-.3em}
  \if@twocolumn
    \small\bfseries{\itshape\keywordsname\/---}%
  \else
    \begin{center}\small\bf\keywordsname\end{center}\quotation\small
  \fi\ignorespaces}
\def\endkeywords{\vspace{0.6em}\par\if@twocolumn\else\endquotation\fi
    \normalsize\normalstyle}

% **************************************************************************
% *****   Fix Section Numbering   ******************************************
% **************************************************************************
\gdef\@punct{.\ \ }  % Punctuation after run-in section heading
\def\@sect#1#2#3#4#5#6[#7]#8{%
  \ifnum #2>\c@secnumdepth
     \def\@svsec\@empty
  \else
     \refstepcounter{#1}%
     \protected@edef\@svsec{%
     %\ifnum #2=1\Roman{#1}.\fi\ifnum #2=2\Alph{#1}.\fi
     \ifnum #2=1\thesection.\fi
     \ifnum #2=2\thesubsection.\fi
     \ifnum #2>2{\csname the#1dis\endcsname}\if@technote.\fi\fi \hskip .5em}
     \ifnum #2=1\ifappendix\stepcounter{numappendices}\fi\fi
  \fi
  \@tempskipa #5\relax
  \ifdim \@tempskipa>\z@
     \begingroup #6\relax
       \@hangfrom{\hskip #3\relax\@svsec}{\interlinepenalty \@M #8\par}
     \endgroup
     \csname #1mark\endcsname{#7}
     \addcontentsline{toc}{#1}{\ifnum #2>\c@secnumdepth\else
               \protect\numberline{\csname the#1\endcsname}\fi#7}
  \else
     \def\@svsechd{#6\hskip #3\@svsec #8\@punct\csname #1mark\endcsname{#7}
     \addcontentsline{toc}{#1}{\ifnum #2>\c@secnumdepth \else
               \protect\numberline{\csname the#1\endcsname}\fi#7}}
  \fi
  \@xsect{#5}}

\def\@ssect#1#2#3#4#5{\@tempskipa #3\relax
  \ifdim \@tempskipa>\z@
     \begingroup #4\@hangfrom{\hskip #1}{\interlinepenalty \@M #5\par}\endgroup
  \else \def\@svsechd{#4\hskip #1\relax #5\@punct}\fi
  \@xsect{#3}}

% **************************************************************************
% *****   Section Definitions   ********************************************
% **************************************************************************
\def\section{\@startsection{section}{1}{\z@}{2.0ex plus .5ex
     minus .2ex}{1.0ex plus .2ex}{\centering\scshape}}
\def\subsection{\@startsection{subsection}{2}{\z@}{2.0ex plus .5ex
     minus .2ex}{1.0ex plus .2ex}{\itshape}}
\if@technote
  \def\subsubsection{\@startsection{subsubsection}{3}{\z@}{2.0ex plus .5ex
     minus .1ex}{0pt}{\itshape}}
\else
  \def\subsubsection{\@startsection{subsubsection}{3}{\z@}{2.0ex plus .5ex
     minus .2ex}{1.0ex plus .2ex}{\normalstyle}}
  \def\paragraph{\@startsection{paragraph}{4}{\z@}{1.0ex plus .5ex
     minus .2ex}{0ex}{\normalstyle}}
\fi

% **************************************************************************
% *****   Special Environment Definitions   ********************************
% **************************************************************************
\def\QED{\mbox{\rule[0pt]{1.5ex}{1.5ex}}}
\def\proof{\noindent\hspace{1em}{\it Proof: }}
\def\endproof{\hspace*{\fill}~\QED\par\endtrivlist\unskip}
\def\@begintheorem#1#2{\tmpitemindent\itemindent\topsep 0pt\normalstyle\trivlist
    \item[\hskip \labelsep{\indent\it #1\ #2:}]\itemindent\tmpitemindent}
\def\@opargbegintheorem#1#2#3{\tmpitemindent\itemindent\topsep 0pt\normalstyle \trivlist
    \item[\hskip\labelsep{\indent\it #1\ #2\ \normalstyle(#3)}]\itemindent\tmpitemindent}
\def\@endtheorem{\endtrivlist\unskip}

% **************************************************************************
% *****   Special Environment Definitions   ********************************
% **************************************************************************
\if@twoside\else\raggedbottom\fi

%% Definition for Big letter at the beginning of a paragraph
%%
\def\PARstart#1#2 {\begingroup\def\par{\endgraf\endgroup\lineskiplimit=0pt}
    \setbox2=\hbox{\uppercase{#2} }\newdimen\tmpht \tmpht \ht2
    \advance\tmpht by \baselineskip\font\hhuge=cmr10 at \tmpht
    \setbox1=\hbox{{\hhuge #1}}
    \count7=\tmpht \count8=\ht1\divide\count8 by 1000 \divide\count7 by\count8
    \tmpht=.001\tmpht\multiply\tmpht by \count7\font\hhuge=cmr10 at \tmpht
    \setbox1=\hbox{{\hhuge #1}} \noindent \hangindent1.05\wd1
    \hangafter=-2 {\hskip-\hangindent \lower1\ht1\hbox{\raise1.0\ht2\copy1}%
    \kern-0\wd1}\copy2\lineskiplimit=-1000pt}

\def\PARstartCal#1#2 {\begingroup\def\par{\endgraf\endgroup\lineskiplimit=0pt}
    \setbox2=\hbox{\uppercase{#2} }\newdimen\tmpht \tmpht \ht2
    \advance\tmpht by \baselineskip\font\hhuge=cmsy10 at \tmpht
    \setbox1=\hbox{{\hhuge #1\/}}
    \count7=\tmpht \count8=\ht1\divide\count8 by 1000 \divide\count7 by\count8
    \tmpht=.001\tmpht\multiply\tmpht by \count7\font\hhuge=cmsy10 at \tmpht
    \setbox1=\hbox{{\hhuge #1\/}} \noindent \hangindent1.05\wd1
    \hangafter=-2 {\hskip-\hangindent \lower1\ht1\hbox{\raise1.0\ht2\copy1}%
    \kern-0\wd1}\copy2\lineskiplimit=-1000pt}

\def\PARstartLyX#1{\PARstart #1}
\def\PARstartCalLyX#1{\PARstartCal #1}

\if@technote\def\PARstart#1#2{#1#2}\fi     % if technical note, disable it
\if@technote\def\PARstartCal#1#2{#1#2}\fi  % if technical note, disable it
\if@technote\def\PARstartLyX#1{#1}\fi      % if technical note, disable it
\if@technote\def\PARstartCalLyx#1{#1}\fi   % if technical note, disable it

% **************************************************************************
% *****   Misc. Definitions   **********************************************
% **************************************************************************
%Restore single spacing
\newcommand{\blsone}{\renewcommand\baselinestretch{1}%
  \renewcommand\arraystretch{1.2}\setlength{\parindent}{\parindentsave}%
  \normalsize}
\newcommand{\capitem}[1]{{\hspace{0.2ex}(#1)}~}
\newcommand{\insdate}{}

% **************************************************************************
% *****   MATH Definitions   ***********************************************
% **************************************************************************
\def\eqnarray{%  
   \stepcounter{equation}%
   \def\@currentlabel{\p@equation\theequation}%
   \global\@eqnswtrue
   \m@th
   \global\@eqcnt\z@
   \tabskip\@centering
   \let\\\@eqncr
   $$\everycr{}\halign to\displaywidth\bgroup
       \hskip\@centering$\displaystyle\tabskip\z@skip{##}$\@eqnsel
      &\global\@eqcnt\@ne\hskip \eqnarr@ysep\hfil${##}$\hfil
      &\global\@eqcnt\tw@ \hskip \eqnarr@ysep
         $\displaystyle{##}$\hfil\tabskip\@centering
      &\global\@eqcnt\thr@@ \hb@xt@\z@\bgroup\hss##\egroup
         \tabskip\z@skip
      \cr
}
\def\endeqnarray{%
      \@@eqncr  
      \egroup
      \global\advance\c@equation\m@ne
   $$\@ignoretrue
}

% **************************************************************************
% *****   Biography Definitions   ******************************************
% **************************************************************************
% This is the main code for the biography environment of the IEEE 
% transactions class. The previous biography code had some known
% problems which were difficult to fix. The crux of the issue was that
% the photo frame was overlaid by text when \baselinestretch>1 or when
% the biography consisted of multiple short paragraphs.
%
% The fix was done by extracting code from the excellent package:
% 'picinpar.sty' version 1.2a as of july 13, 1993
% by Friedhelm Sowa
%
% (At least most of) The bugs you find in this code were introduced
% unwittingly by myself.
%
%----------------
% Known problems:
%
%    - Don't use multiple blank lines to separate paragraphs. A single
%      blank line works well, but multiple blank lines will confuse
%      the code. This has something to do with the \def\par{\\\indent} 
%      line, but I can't think of an appropriate fix. Similarly, make
%      sure the environment doesn't end with an extra blank line.
%    - Don't use \samepage
%    - Use \footnotemark within and \footnotetext outside the
%      window-environment instead of \footnote
%    - When using the epic-package load picinpar before epic
%      like \documentstyle[...,picinpar,epic]{...}
%
% Counts
\newcount\br \newcount\nb \newcount\tcdsav \newcount\tcl \newcount\tcd
\newcount\tcn \newcount\cumtcl 
% Dimens
\newdimen\rtside \newdimen\hpic \newdimen\vpic \newdimen\strutilg
\newdimen\picwd \newdimen\topheight \newdimen\ilg \newdimen\lpic
\newdimen\lwindowsep \newdimen\rwindowsep	% VK 10 Feb 93
\lwindowsep0.5\baselineskip			% "
\rwindowsep0.5\baselineskip			% "
\newdimen\cumpar
% Tokens
\newtoks\twa \newtoks\la \newtoks\ra \newtoks\ha \newtoks\pictoc
% Boxes
\newbox\rawtext \newbox\holder \newbox\windowbox \newbox\wartext
\newbox\finaltext \newbox\aslice \newbox\bslice \newbox\wbox
\newbox\wstrutbox \newbox\picbox \newbox\waslice \newbox\wbslice
\newbox\fslice
 % Another strut
\def\wstrut{\relax\ifmmode\copy\wstrutbox\else\unhcopy\wstrutbox\fi}
%

\def\getpic#1{\sbox{\@tempboxa}{\includegraphics{#1}}%
\newcount\tmpcta \tmpcta=\ht\@tempboxa%
\newcount\tmpctb \tmpctb=\wd\@tempboxa%
\divide\tmpctb by 100%
\divide\tmpcta by\tmpctb%
\ifnum\tmpcta>133%
\typeout{ieee: Biography picture `#1' too tall.}%
\frame{\hbox to 25mm{\hfil\resizebox{!}{32mm}{\usebox{\@tempboxa}}\hfil}}%
\else \ifnum\tmpcta<123%
\typeout{ieee: Biography picture `#1' too wide.}%
\frame{\vbox to 32mm{\vss\hbox{\resizebox{25mm}{!}{\usebox{\@tempboxa}}}\vss}}%
\else%
\resizebox{25mm}{32mm}{\usebox{\@tempboxa}}
\fi\fi}

\long\def\biographyLyX#1{\if@non\else\begin{biography} #1\end{biography}\fi}

\if@non
  \long\def\biography{}
\else
  \long\def\biography{\@ifnextchar [{\@biographyb}{\@biographya[{\unitlength 
  1mm\hbox{\framebox(25,32){}}}]}}
\fi

\long\def\@biographyb[#1]{\@biographya[\getpic{#1}]}

\long\def\@biographya[#1]#2{\bgroup
\footnotesize\bigskip\bigskip\bigskip\parskip=0pt\par%
\rule{0pt}{35mm}\vspace*{-35mm}\par%   garantees correct page breaking
\begin{main@bio}[{#1}]%
\noindent{\bf #2}%
}
\def\endbiography{\if@non\else\end{main@bio}\egroup\fi}

\long\def\main@bio[#1]{% #1 is the material for setting a graphic box
\vskip\parskip\everypar{}
\global\cumpar=0pt
\global\cumtcl=0
    \tcd=0
    \rtside=0pt
%    \hpic=\linewidth
    \twa={} \la={} \ra={} \ha={}
\setbox\wbox=\hbox{(}
\computeilg
\pictoc={#1}
\setbox\windowbox=\vbox{\hbox{#1}}
\picwd=\wd\windowbox
\hpic=\picwd
\vpic=\ht\windowbox\advance\vpic\dp\windowbox
\rtside=\linewidth\advance\rtside-\picwd
\setbox\picbox=\vbox{\hsize=\hpic\vbox to\vpic{\box\windowbox}}% \vfill}}%

\vpic=\ht\picbox\advance\vpic\dp\picbox
\ifdim\rtside>0pt\advance\rtside-\rwindowsep\fi    % "
\global\br=\rtside
\ifnum\picwd=0
\ifdim\vpic>0pt\picwd=\hpic
\else\vpic=\ht\picbox\advance\vpic\dp\picbox
\fi
\fi
    \global\tcl=0 \lpic=0pt
    \loop\global\advance\tcl by 1 \lpic=\tcl\baselineskip
    \ifdim\lpic<\vpic\repeat
    \vpic=\lpic
    \global\cumtcl=\tcl
%
% Here we know exactly the number of indented lines and
% are able to generate the tokens for the \parshape list
%
    \ifnum\br>0\ra={ 0pt \rtside}\fi
    \ifnum\tcd>0\ha={ 0pt \linewidth}\fi
    \ifnum\tcl<1\global\tcl=1\fi
    \createparshapespec
    \tcd=0                        % restore the lintel
    \global\tcdsav=0
%
% This is a very tricky part of the package. Some day there
% will exist a detailed documentation.
%
\def\par{\\\indent}
%
% This is where we start to pick up the paragraph(s)
%
    \setbox\rawtext=\vbox\bgroup\unvbox\rawtext\unskip
    \clubpenalty=0\widowpenalty=0
    \ifnum\brokenpenalty<\maxdimen\else\brokenpenalty=9999\fi
    \tolerance=1000
    \parshape=\tcn \the\twa }
%
\def\endmain@bio{%
    %\par
    \global\tcd=\tcdsav
    \egroup\vskip\parskip\parshape=0 % reset parshape; end \box\rawtext
    \vbadness=10000
    \splittopskip=0pt
%
% Now we build the boxes beside the window
%
\global\topheight=\tcl\baselineskip
\ifnum\br>0\setbox\holder=\vsplit\rawtext to\topheight\fi
\tcn=\tcl \nb=0
\ifnum\br>0\nb=\tcn\fi
%
% text on the right side
%
\ifnum\nb>0
    \loop\advance\nb -1
    \setbox\bslice=\vsplit\holder to\baselineskip
    \prune\bslice\rtside
    \setbox\wbslice=\vbox{\unvbox\wbslice\hbox
    to\rtside{\box\bslice\hfil}}
    \ifdim\ht\holder>0pt\repeat
\fi
%GLP add fix to make sure bio starts at top of picture
\setbox\wbslice=\vbox to\topheight{\unvbox\wbslice\vfill\vss}
%
% fixing the dimensions of the window part
%
\topheight=\ht\wbslice
%
% ship out the window material to the main vertical list
%
\setbox\windowbox=\vbox{\hbox to\linewidth{%
\vbox to\topheight{\hrule width\picwd height0pt depth0pt\vskip0pt%
\vfill\unvbox\picbox%
\ifnum\picwd>0\vfill\fi%
\vss}\ifnum\br>0\hfill\vbox{\box\wbslice}\fi}}%
%
\unvbox\windowbox%
\loop% lines below picture....
 \setbox\bslice=\vsplit\rawtext to\baselineskip
 \prune\bslice\linewidth
 \setbox\wbslice=\vbox{\hbox to\linewidth{\box\bslice\hfil}}
 \unvbox\wbslice
 \ifdim\ht\rawtext>0pt
\repeat
%GLP
%\ifnum\nb>0\topheight=\nb\baselineskip %\advance\topheight by\ilg
%\vspace*{\topheight}
%\fi
}% FINITO
%
% What else do we need?
%
\def\prune#1#2{
% take a \vbox containing a single \hbox,
% \unvbox it, and cancel the \lastskip
% put in a \hbox of width #2
 \unvbox#1 \setbox#1=\lastbox % \box#1 now is an \hbox
 \ifdim\ht#1=\parskip
 \setbox#1=\hbox to#2{\vrule height\parskip depth0pt width0pt\hfill}
 \else\ifdim\ht#1=0pt\relax
 \else\setbox#1=\hbox to#2{\wstrut\unhbox#1\unskip}\fi\fi}
%
% Here the token \twa is generated.
% It's not so difficult as it looks like.
%
\def\createparshapespec{%
\global\tcn=0
\ifnum\br>0\global\tcn=\tcl\fi
\nb=0
\ifnum\br>0\nb=\tcn\fi
\global\advance\tcn by\tcd \global\advance\tcn by1
\ifnum\tcd>0
\loop\twa=\expandafter{\the\twa\the\ha}\advance\tcd -1
\ifnum\tcd>0\repeat
\fi
\ifnum\nb>0
\loop\twa=\expandafter{\the\twa\the\ra}\advance\nb -1
\ifnum\nb>0\repeat
\fi
\global\twa=\expandafter{\the\twa 0pt \the\linewidth}}
%
\def\computeilg{% compute the interline glue
 \tcl=0\ilg=0pt\strutilg=0pt
 \loop\setbox\wbox=\hbox{\char\tcl}
 \ifdim\ht\wbox>\ilg\ilg=\ht\wbox\fi
 \ifdim\dp\wbox>\strutilg\strutilg=\dp\wbox\fi
 \advance\tcl by 1
 \ifnum\tcl<128\repeat
 \ht\wbox=\ilg
 \dp\wbox=\strutilg
 \strutilg=\ht\wbox %\advance\strutilg by\ilg
 \ifdim\strutilg>\baselineskip
  \typeout{character with height greater baselineskip found in font}
  \typeout{baselineskip changed to 1.5 of that height!}
  \baselineskip=1.5\strutilg
 \fi
 \global\ilg=\baselineskip
 \global\advance\ilg-\ht\wbox \global\advance\ilg-\dp\wbox
 \strutilg=\ht\wbox \advance\strutilg by\ilg
 \setbox\wstrutbox=\hbox{\vrule height\strutilg depth\dp\wbox width0pt}}


% the following code from version.sty by Stephen Bellantoni 1990, loosely 
% based on "annotation.sty" by Tom Hofmann. Used to exclude "biography" from 
% anonymous mode.
\begingroup
\catcode`@=11\relax%
\catcode`{=12\relax\catcode`}=12\relax%
\catcode`(=1\relax \catcode`)=2\relax%
\gdef\glpinclude#1(%
  \expandafter\gdef\csname #1\endcsname%
    ()%
  \expandafter\gdef\csname end#1\endcsname%
    ()%
)%
\gdef\glpexclude#1(%
  \expandafter\gdef\csname #1\endcsname%
    (\@bsphack\catcode`{=12\relax\catcode`}=12\relax\csname #1@NOTE\endcsname)%
  \long\expandafter\gdef\csname #1@NOTE\endcsname ##1\end{#1}%
    (\csname #1END@NOTE\endcsname)%
  \expandafter\gdef\csname #1END@NOTE\endcsname%
    (\@esphack\end(#1))%
)%
\endgroup

%-------
\def\@confplacedate{\typeout{ieee: Warning! No \noexpand\confplacedate set!}
\bfseries `confplacedate' needs to be set. For example, to: Stanford, CA, USA, 
September 29--30, 1991}
\def\confplacedate#1{\def\@confplacedate{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%% End of ieee.cls  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
