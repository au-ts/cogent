from random import seed,randint

if __name__ == "__main__":
    seed()
    with open("entries.txt", 'w') as f:
        for i in xrange(1000):
            f.write("{0} {1} {2} {3}\n".format(randint(30,999),
                                               randint(30,999),
                                               randint(30,999),
                                               randint(1,100)))
