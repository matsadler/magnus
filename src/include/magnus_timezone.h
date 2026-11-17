#ifndef MAGNUS_TIMEZONE_H
#define MAGNUS_TIMEZONE_H

#include <stdint.h>

/* Public jiff-zoned timezone TypedData ABI, version 1. Use normal C alignment. */
#define MAGNUS_TIMEZONE_TYPE_NAME "magnus-jiff-timezone"
#define MAGNUS_TIMEZONE_ABI_VERSION UINT8_C(1)
#define MAGNUS_TIMEZONE_MAX_BYTES 128
#define MAGNUS_TIMEZONE_UNREPRESENTABLE "magnus:timezone:unrepresentable"

struct MagnusTimeZone {
    /* Must equal MAGNUS_TIMEZONE_ABI_VERSION. Check before reading later fields. */
    uint8_t abi_version;

    /*
     * Requirements:
     * - Non-NULL, immutable, NUL-terminated UTF-8 in Jiff's Temporal timezone
     *   format.
     * - The terminator must occur within MAGNUS_TIMEZONE_MAX_BYTES bytes.
     *   Reject strings without a terminator in that range; scan no further.
     * - Providers must supply readable storage through the terminator. The byte
     *   limit does not validate an arbitrary native pointer.
     *
     * A Ruby timezone object implementing this ABI owns a TypedData allocation
     * that begins with this MagnusTimeZone header. The jiff_timezone field
     * points to a string owned by the same object. The header and string stay
     * at stable addresses and remain valid while that Ruby object is alive.
     *
     * C readers validate the TypedData descriptor name and ABI version before
     * reading this field. Keep the owning Ruby VALUE, timezone_object, in a
     * local variable and call RB_GC_GUARD(timezone_object) after the last read
     * through either borrowed pointer. Copy the string into reader-owned
     * storage to retain it after releasing the Ruby object. Never free the
     * borrowed pointers or read past the MagnusTimeZone header.
     *
     * Names resolve in the reader's database, so database differences and
     * custom named TZif can lose source rules. Unprintable or oversized
     * representations use MAGNUS_TIMEZONE_UNREPRESENTABLE rather than TZif
     * snapshots. Reject that marker before parsing; Etc/Unknown is valid.
     * https://docs.rs/jiff/1.0.0/jiff/fmt/temporal/struct.DateTimePrinter.html#method.time_zone_to_string
     */
    const char *jiff_timezone;
};

#endif
