# python -m decider.multithread
import queue
import time
from decider.isv import isv
from decider.utils import parse_file, unparse_line
from os import cpu_count
from multiprocessing import Manager, Process

'''
Run other deciders with multithreading.
'''


def run_decider(F: list[list[int]]) -> str | None:
    # return isv(F, 0)
    return isv(F, 1000)
    # return None


def worker(holdouts_in: queue.Queue, holdouts_out1: queue.Queue, holdouts_out2: queue.Queue):
    while True:
        try:
            item = holdouts_in.get(block=False)
        except queue.Empty:
            return
        i, holdout = item
        result = run_decider(holdout)
        if result is not None:
            holdouts_out1.put((i, holdout, result))
        else:
            holdouts_out2.put((i, holdout))
        holdouts_in.task_done()


if __name__ == '__main__':
    threads = max(2, (cpu_count() or 1)*9//10)
    holdouts = parse_file('holdout/sz22_9829.txt')
    print(f'running {threads} threads on {len(holdouts)} holdouts')

    with Manager() as manager:
        # input, decided output, undecided output
        holdouts_in = manager.Queue()  # has tuple[int, list[list[int]]]
        holdouts_out1 = manager.Queue()  # has tuple[int, list[list[int]], str]
        holdouts_out2 = manager.Queue()  # has tuple[int, list[list[int]]]

        for i, F in enumerate(holdouts):
            holdouts_in.put((i, F))

        time1 = time.time()
        tt = [Process(target=worker, args=(holdouts_in, holdouts_out1,
                                           holdouts_out2), name=f'worker-{i}') for i in range(threads)]
        for t in tt:
            t.start()
        holdouts_in.join()
        for t in tt:
            t.join()
        time2 = time.time()
        print(f'elapsed time: {time2-time1}')

        out1 = []
        while True:
            try:
                out1.append(holdouts_out1.get(block=False))
            except queue.Empty:
                break
        print(f'{len(out1)} holdouts decided')
        out1.sort()
        with open('decider/tmp_multithread_1.txt', 'w') as f:
            for _, F, result in out1:
                f.write(f'{unparse_line(F)}, NON-HALT: {result}\n')

        out2 = []
        while True:
            try:
                out2.append(holdouts_out2.get(block=False))
            except queue.Empty:
                break
        print(f'{len(out2)} holdouts remaining')
        out2.sort()
        with open('decider/tmp_multithread_2.txt', 'w') as f:
            for _, F in out2:
                f.write(f'{unparse_line(F)}\n')
