% Author: Hsieh, Chiao
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{ntuthesis}[2015/05/08 NTU Thesis Class]

%% Fallback
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{book}}

\ProcessOptions\relax

\LoadClass[a4paper, 12pt]{book} % Based on "book" class

\RequirePackage[top=3cm,left=3cm,bottom=2cm,right=3cm]{geometry} % Set layout
\RequirePackage{CJKutf8} % Support Traditional Chinese
\RequirePackage{newtxtext} % Times New Roman like font
\RequirePackage{etoolbox} % Automatically generate newcommands
\RequirePackage[usenames]{xcolor} % Colored text
\RequirePackage{datetime} % Show current month and year
\RequirePackage{fp} % Simple calculations on years
\RequirePackage{setspace} % Line spacing

\pagestyle{plain} % Set header and footer style

%% Generate newcommand according to a list
\newcommand{\ListOfFields}[1]{
  \renewcommand*{\do}[1]{% \do to eaZH item in list
    % Define commands with no argument as variables
    \expandafter\newcommand\csname @##1ZH\endcsname{\textcolor{red}{set##1ZH}}
    \expandafter\newcommand\csname @##1EN\endcsname{\textcolor{red}{set##1EN}}
    % Define updating commands
    \expandafter\newcommand\csname set##1ZH\endcsname[1]{
      \expandafter\renewcommand\csname @##1ZH\endcsname{####1}
    }
    \expandafter\newcommand\csname set##1EN\endcsname[1]{
      \expandafter\renewcommand\csname @##1EN\endcsname{####1}
    }
  }
  \docsvlist{#1}% Process list
}
%% List all necessary fields
\ListOfFields{University,College,Institute,ThesisType,Title,Author,AdvisorName,AdvisorTitle,GradYear,GradMonth}

%% Set initial values
\setUniversityZH{國立臺灣大學}
\setGradYearZH  {\FPeval{\result}{round(\the\year-1911,0)}\result}
\setGradMonthZH {\the\month}

\setUniversityEN{National Taiwan University}
\setGradYearEN  {\the\year}
\setGradMonthEN {\monthname}

%% Make title page
\renewcommand{\maketitle}{
\newgeometry{top=3cm, bottom=3cm}
\begin{titlepage}
\begin{center}
 \fontsize{18pt}{27pt}\selectfont
  \@UniversityZH\@CollegeZH\@InstituteZH\\
  \@ThesisTypeZH

{ \fontsize{14pt}{21pt}\selectfont
  \@InstituteEN\\
  \@CollegeEN\\
}{\fontsize{16pt}{24pt}\selectfont
  \@UniversityEN\\
  \@ThesisTypeEN
}

  \vspace{2cm}
{%\parbox[c][150pt][c]{\textwidth}{
  \@TitleZH\\
  \@TitleEN
}

  \vspace*{\fill}
  \@AuthorZH\\
  \@AuthorEN

  \vspace{1.5cm}
  指導教授：\@AdvisorNameZH~\@AdvisorTitleZH\\
  Advisor: \@AdvisorNameEN, \@AdvisorTitleEN

  \vspace{1.5cm}
  中華民國~\raisebox{1pt}{\@GradYearZH}~年~\raisebox{1pt}{\@GradMonthZH}~月\\
  \@GradMonthEN~\@GradYearEN
\end{center}
\end{titlepage}
\restoregeometry
}

\endinput
