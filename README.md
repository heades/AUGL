The Augusta Agda Library (AUGL)
-------------------------------

This is my personal Agda library.  It is based on the Iowa Agda
Library to which the I was a contributor, but our interests shifted
and we thought it best to split the library.

- About the library

  The goal of this project is to develop a library focused on the
  verification of results in categorical logic.

- Using the library

  This library is known to work with Agda 2.4.2.3/2.4.2.2/2.4.2.1.

  In Agda, you can include the whole library by importing lib.agda.

  You can compile the whole library by running "make".

  The library is set up so there are no name conflicts between modules
  (except sometimes I have several versions of the same module, like
  stream and stream2 or nat-division and nat-division2, and there
  might be name conflicts in such cases).

- Browsing the library

  You can get some overview of what is in the library by following
  imports from lib.agda (this is the main entry point for the
  library).

- License

This library is currently provided under the MIT License, see LICENSE.txt.

- Documentation

There is no formal documentation currently, besides comments in the files.

