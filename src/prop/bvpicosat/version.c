#include "config.h"

const char *
picosat_version (void)
{
  return PICOSAT_VERSION;
}

const char *
picosat_config (void)
{
  return PICOSAT_CC " " PICOSAT_CFLAGS;
}

