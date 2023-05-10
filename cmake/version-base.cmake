# These are updated when making a release
set(CVC5_LAST_RELEASE "1.0.5")
set(CVC5_IS_RELEASE "false")

# These are used in other places in cmake
# If possible, they are updated by version.cmake
set(GIT_BUILD "false")
set(CVC5_VERSION "${CVC5_LAST_RELEASE}")
set(CVC5_FULL_VERSION "${CVC5_LAST_RELEASE}")
set(CVC5_GIT_INFO "")

# Shared library versioning. Increment SOVERSION for every new cvc5 release.
set(CVC5_SOVERSION 1)
