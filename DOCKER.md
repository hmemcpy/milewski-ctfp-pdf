Building from Docker
--------

Create the docker image
```
$ docker image build -t milewski-ctfp-pdf:1.0 .
```

Run it interactively starting the nix-shell
```
$ docker container run -i -t --name ctfp milewski-ctfp-pdf:1.0 nix-shell
```

Follow build directions in [README.md](./README.md)

Copy build artifact(s) to local filesystem
```
docker cp ctfp:/usr/git/milewski-ctfp-pdf/out/... destfile
```