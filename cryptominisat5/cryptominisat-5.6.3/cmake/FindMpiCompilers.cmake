# - Find the MPI compiler wrappers
# This module locates the MPI compiler wrappers (mpicc, mpicxx/mpic++, mpif77 and mpif90).
# It is useful if one wants to force a project to use the MPI compiler wrappers as default
# compilers.
#
# The module has the following COMPONENTS:
#  C    searches for mpicc
#  CXX  searches for mpicxx and mpic++
#  F77  searches for mpif77
#  F90  searches for mpif90
# If no components are specified, all of them are enabled by default.
#
# The module sets the following cache variables (if the corresponding module is enabled):
#  MPICOMPILERS_C    the mpicc compiler
#  MPICOMPILERS_CXX  the mpicxx/mpic++ compiler
#  MPICOMPILERS_F77  the mpif77 compiler
#  MPICOMPILERS_F90  the mpif90 compiler
#
# If the user wishes to specify a specific compiler wrapper (e.g. one which is
# using a non-standard name or one which is not found on the path) can do so
# by setting the corresponding MPICOMPILERS_XXX variable (e.g. using the
# -D flag the first time CMake is run). It also honours environment variables
# by the same name. The CC, CXX and similar variables are not considered by
# design.
#
# If the module is not REQUIRED make sure to check the MPICOMPILERS_XXX
# variables.
#
# Beware that although the module can search for both the mpif77 andmpif90
# compiler wrappers, CMake only knows the CMAKE_Fortran_COMPILER variable
# which means that you can't use both of the wrappers in the same project. This,
# however, probably is not a big issue as Fortran90 is a superset of
# Fortran77 and all Fortran90 compilers I know of also process Fortran77
# sources.
#
# An example CMakeLists.txt could look like this:
#
#  # prevent CMake from compiler detection using NONE as the project language
#  project( some_project NONE )
#
#  cmake_minimum_required( VERSION 2.6 )
#
#  # find the mpi compiler wrappers
#  find_package( MpiCompilers REQUIRED CXX F77 )
#
#  # set the CMAKE_XXX_COMPILER variables
#  set( CMAKE_CXX_COMPILER ${MPICOMPILERS_CXX} )
#  set( CMAKE_Fortran_COMPILER ${MPICOMPILERS_F77} )
#  # enable the corresponding languages to do the compiler detection
#  enable_language( CXX )
#  enable_language( Fortran )
#
#  # now go on as usual
#  add_executable( fancy_mpi_program source1.cxx source2.f )

# Copyright 2009 Michael Wild <themiwi at users.sourceforge.net>

# check the components that are requested
if( MpiCompilers_FIND_COMPONENTS )
   set( __MpiCompilers_C FALSE )
   set( __MpiCompilers_CXX FALSE )
   set( __MpiCompilers_F77 FALSE )
   set( __MpiCompilers_F90 FALSE )
   foreach( __MpiCompilers_comp ${MpiCompilers_FIND_COMPONENTS} )
     if( __MpiCompilers_comp STREQUAL C )
       set( __MpiCompilers_C TRUE )
     elseif( __MpiCompilers_comp STREQUAL CXX )
       set( __MpiCompilers_CXX TRUE )
     elseif(__MpiCompilers_comp STREQUAL F77 )
       set( __MpiCompilers_F77 TRUE )
     elseif( __MpiCompilers_comp STREQUAL F90 )
       set( __MpiCompilers_F90 TRUE )
     else( __MpiCompilers_comp STREQUAL C )
       message( FATAL_ERROR "Unknown component ${__MpiCompilers_comp}" )
     endif( __MpiCompilers_comp STREQUAL C )
   endforeach( __MpiCompilers_comp )
else( MpiCompilers_FIND_COMPONENTS )
   # by default turn all components on
   set( __MpiCompilers_C TRUE )
   set( __MpiCompilers_CXX TRUE )
   set( __MpiCompilers_F77 TRUE )
   set( __MpiCompilers_F90 TRUE )
endif( MpiCompilers_FIND_COMPONENTS )

# find the requested compilers and set up the list
# of required variables
set( __MpiCompilers_REQVARS "" )
set( __MpiCompilers_FOUNDCOMPILERS "" )
if( __MpiCompilers_C )
   if( NOT "$ENV{MPICOMPILERS_C}" STREQUAL "" )
     set( MPICOMPILERS_C $ENV{MPICOMPILERS_C} CACHE FILEPATH "Path to  
the MPI C compiler" )
   else( NOT "$ENV{MPICOMPILERS_C}" STREQUAL "" )
     find_program( MPICOMPILERS_C mpicc DOC "Path to the MPI C  
compiler" )
   endif( NOT "$ENV{MPICOMPILERS_C}" STREQUAL "" )
   list( APPEND __MpiCompilers_REQVARS MPICOMPILERS_C )
   set( __MpiCompilers_FOUNDCOMPILERS "$ 
{__MpiCompilers_FOUNDCOMPILERS} ${MPICOMPILERS_C}" )
endif( __MpiCompilers_C )
if( __MpiCompilers_CXX )
   if( NOT "$ENV{MPICOMPILERS_CXX}" STREQUAL "" )
     set( MPICOMPILERS_CXX $ENV{MPICOMPILERS_CXX} CACHE FILEPATH "Path  
to the MPI C++ compiler" )
   else( NOT "$ENV{MPICOMPILERS_CXX}" STREQUAL "" )
     find_program( MPICOMPILERS_CXX NAMES mpicxx mpic++ DOC "Path to  
the MPI C++ compiler" )
   endif( NOT "$ENV{MPICOMPILERS_CXX}" STREQUAL "" )
   list( APPEND __MpiCompilers_REQVARS MPICOMPILERS_CXX )
   set( __MpiCompilers_FOUNDCOMPILERS "$ 
{__MpiCompilers_FOUNDCOMPILERS} ${MPICOMPILERS_CXX}" )
endif( __MpiCompilers_CXX )
if( __MpiCompilers_F77 )
   if( NOT "$ENV{MPICOMPILERS_F77}" STREQUAL "" )
     set( MPICOMPILERS_F77 $ENV{MPICOMPILERS_F77} CACHE FILEPATH "Path  
to the MPI F77 compiler" )
   else( NOT "$ENV{MPICOMPILERS_F77}" STREQUAL "" )
     find_program( MPICOMPILERS_F77 mpif77 DOC "Path to the MPI F77  
compiler" )
   endif( NOT "$ENV{MPICOMPILERS_F77}" STREQUAL "" )
   list( APPEND __MpiCompilers_REQVARS MPICOMPILERS_F77 )
   set( __MpiCompilers_FOUNDCOMPILERS "$ 
{__MpiCompilers_FOUNDCOMPILERS} ${MPICOMPILERS_F77}" )
endif( __MpiCompilers_F77 )
if( __MpiCompilers_F90 )
   if( NOT "$ENV{MPICOMPILERS_F90}" STREQUAL "" )
     set( MPICOMPILERS_F90 $ENV{MPICOMPILERS_F90} CACHE FILEPATH "Path  
to the MPI F90 compiler" )
   else( NOT "$ENV{MPICOMPILERS_F90}" STREQUAL "" )
     find_program( MPICOMPILERS_F90 mpif90 DOC "Path to the MPI F77  
compiler" )
   endif( NOT "$ENV{MPICOMPILERS_F90}" STREQUAL "" )
   list( APPEND __MpiCompilers_REQVARS MPICOMPILERS_F90 )
   set( __MpiCompilers_FOUNDCOMPILERS "$ 
{__MpiCompilers_FOUNDCOMPILERS} ${MPICOMPILERS_F90}" )
endif( __MpiCompilers_F90 )

mark_as_advanced( ${__MpiCompilers_REQVARS} )

# handle standard arguments
include( FindPackageHandleStandardArgs )
find_package_handle_standard_args( MpiCompilers DEFAULT_MSG  
__MpiCompilers_FOUNDCOMPILERS ${__MpiCompilers_REQVARS} )

