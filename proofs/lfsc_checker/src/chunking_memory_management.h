///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//  Copyright (C) 2002 by the Board of Trustees of Leland Stanford           //
//  Junior University.  See LICENSE for details.                             //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/* chunking_memory_management.h 
   Aaron Stump, 6/11/99

   This file contains macros that allow you easily to add chunking
   memory management for classes.

   RCS Version: $Id: chunking_memory_management.h,v 1.1 2004/11/12 16:26:19 stump Exp $

*/
#ifndef _chunking_memory_management_h_
#define _chunking_memory_management_h_

#include <assert.h>

/************************************************************************
 * MACRO: ADD_CHUNKING_MEMORY_MANAGEMENT_H()
 * Aaron Stump, 6/11/99
 *
 * ABSTRACT: This macro should be called exactly once inside the body
 * of the declaration of the class THE_CLASS to add chunking memory
 * management for the class.  That class should not itself declare the
 * operators new and delete.  The macro
 * C_MACROS__ADD_CHUNKING_MEMORY_MANAGEMENT_CC should be called with
 * the same value for THE_CLASS in a .cc file for that class.
 *
 * NOTE that the access specifier will be public after calling this 
 * macro.
 *
 * THE_FIELD is a field of the class to use for the next pointer in the
 * free list data structure.  It can be of any type, but must have enough
 * space to hold a pointer.
 ************************************************************************/
#define C_MACROS__ADD_CHUNKING_MEMORY_MANAGEMENT_H(THE_CLASS,THE_FIELD)	\
private:\
  static unsigned C_MACROS__CHUNK_SIZE;\
  static unsigned C_MACROS__BLOCK_SIZE;\
  static void *C_MACROS__freelist;\
  static bool C_MACROS__initialized;\
  static char *C_MACROS__next_free_block;\
  static char *C_MACROS__end_of_current_chunk;\
  \
  static void C_MACROS__allocate_new_chunk();\
\
public:\
  static void C_MACROS__init_chunks() {\
    if (!C_MACROS__initialized) {\
      C_MACROS__allocate_new_chunk();\
      C_MACROS__initialized = true;\
    }\
  }\
\
  static void *operator new(size_t size, void *h = NULL);\
  static void operator delete(void *ptr)\


/************************************************************************
 * MACRO: ADD_CHUNKING_MEMORY_MANAGEMENT_CC()
 * Aaron Stump, 6/11/99
 *
 * ABSTRACT: This macro should be called exactly once in a .cc file
 * for the class THE_CLASS to add chunking memory management for the
 * class.  This macro should be called with the same value for
 * THE_CLASS as was used in calling
 * C_MACROS__ADD_CHUNKING_MEMORY_MANAGEMENT_H in the body of the
 * declaration of THE_CLASS.  THE_CHUNK_SIZE is the number of blocks
 * of memory to get at once using malloc().  A block is the portion
 * of memory needed for one instance of THE_CLASS.
 *
 *
 * IMPLEMENTATION:
 ************************************************************************
 * FUNCTION: allocate_new_chunk()
 * Aaron Stump, 6/8/99
 *
 * ABSTRACT: This method allocates a new chunk of memory to use for
 * allocating instances of THE_CLASS.
 ************************************************************************
 * FUNCTION: new()
 * Aaron Stump, 6/8/99
 *
 * ABSTRACT: This allocator uses chunks for more efficient allocation.
 ************************************************************************
 * FUNCTION: delete()
 * Aaron Stump, 6/8/99
 *
 * ABSTRACT: This delete() puts the chunk pointed to by ptr on the 
 * freelist.
 ************************************************************************
 * Chunking_Memory_Management_Initializer and its static instance are used
 * to call the static init_chunks() method for THE_CLASS. 
 ************************************************************************/
#define C_MACROS__ADD_CHUNKING_MEMORY_MANAGEMENT_CC(THE_CLASS,THE_FIELD,THE_CHUNK_SIZE) \
unsigned THE_CLASS::C_MACROS__CHUNK_SIZE = THE_CHUNK_SIZE;\
\
unsigned THE_CLASS::C_MACROS__BLOCK_SIZE = sizeof(THE_CLASS);\
\
void * THE_CLASS::C_MACROS__freelist = NULL;\
char * THE_CLASS::C_MACROS__next_free_block = NULL;\
char * THE_CLASS::C_MACROS__end_of_current_chunk = NULL;\
bool THE_CLASS::C_MACROS__initialized = false;\
\
void \
THE_CLASS::C_MACROS__allocate_new_chunk() {\
\
  unsigned tmp = C_MACROS__CHUNK_SIZE * C_MACROS__BLOCK_SIZE;\
  char *chunk = (char *)malloc(tmp);\
  \
  assert (chunk != NULL);			\
\
  C_MACROS__next_free_block = chunk;\
  C_MACROS__end_of_current_chunk = chunk + tmp;\
}\
\
void * \
THE_CLASS::operator new(size_t size, void *h) {\
  (void)size; /* size should always be _BLOCK_SIZE */\
\
  if (h != NULL)\
    /* we're being told what memory we should use */\
    return h;\
\
  char *new_block;\
\
  if (C_MACROS__freelist) {\
    /* we have a block on the freelist that we can use */\
    new_block = (char *)C_MACROS__freelist;			\
    C_MACROS__freelist = (void *)((THE_CLASS *)new_block)->THE_FIELD;	\
  }\
  else {\
    /* we have to get a new block from a chunk (which we may */\
    /* have to allocate*/\
    \
    if (C_MACROS__next_free_block == C_MACROS__end_of_current_chunk)\
      C_MACROS__allocate_new_chunk();\
    \
    new_block = C_MACROS__next_free_block;\
    C_MACROS__next_free_block += C_MACROS__BLOCK_SIZE;\
  }\
  \
  return new_block;\
}\
\
void \
THE_CLASS::operator delete(void *ptr) {\
  void **f = (void **)&((THE_CLASS *)ptr)->THE_FIELD;	\
  *f = C_MACROS__freelist;	\
  C_MACROS__freelist = ptr;				      \
}

#endif

