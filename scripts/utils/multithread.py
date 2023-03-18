import threading


print_lock = threading.Lock()


def thread_safe_print(*args, **kwargs):
    with print_lock:
        print(*args, **kwargs)
