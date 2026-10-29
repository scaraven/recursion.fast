"""Reading files an untrusted process wrote (TRUSTED RUNTIME). A prover controls everything under
its directory: a name may be a symbolic link to a host file, a FIFO that blocks a reader, or a
huge file. `read_output` follows no link at any component, opens without blocking, and accepts
only a regular file within a size cap."""
import os
import stat


class OutputError(Exception):
    pass


def read_output(base: str, rel: str, cap: int) -> bytes:
    """The bytes of the regular file `base/rel`, at most `cap` bytes, no link followed."""
    parts = [p for p in rel.split("/") if p]
    if not parts or any(p in (".", "..") for p in parts):
        raise OutputError(f"bad output name {rel!r}")
    fd = os.open(base, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for p in parts[:-1]:
            nfd = os.open(p, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = nfd
        try:
            ffd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
        except FileNotFoundError:
            raise OutputError(f"{rel}: missing")
        except OSError as e:
            raise OutputError(f"{rel}: cannot open ({e.strerror})")
    except NotADirectoryError:
        raise OutputError(f"{rel}: a component is not a directory")
    except OSError as e:
        raise OutputError(f"{rel}: {e.strerror}")
    finally:
        os.close(fd)
    try:
        st = os.fstat(ffd)
        if not stat.S_ISREG(st.st_mode):
            raise OutputError(f"{rel}: not a regular file")
        if st.st_size > cap:
            raise OutputError(f"{rel}: {st.st_size} bytes, above the cap of {cap}")
        chunks, left = [], cap + 1
        while left > 0:
            c = os.read(ffd, min(left, 1 << 20))
            if not c:
                break
            chunks.append(c)
            left -= len(c)
        data = b"".join(chunks)
        if len(data) > cap:
            raise OutputError(f"{rel}: grew above the cap of {cap}")
        return data
    finally:
        os.close(ffd)
