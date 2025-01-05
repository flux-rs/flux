# For a demo container:
# docker build --tag=flux .
# To run tests:
# docker build --target=test .

# NOTE: liquid-fixpoint and z3 versions are not pinned,
# watch out for breaking changes

# uses official haskell image containing cabal and stack by default
ARG FIXPOINT_BUILDER="docker.io/library/haskell:9.10.1-bullseye"

# ARG BASE_IMAGE requirements:
# - debian-based because it uses apt-get to install z3
# - cargo is available
ARG BASE_IMAGE="docker.io/library/rust:1.83-bullseye"

FROM $FIXPOINT_BUILDER as fixpoint-builder
WORKDIR /

RUN \
  git clone --single-branch \
  https://github.com/ucsd-progsys/liquid-fixpoint.git \
  && cd /liquid-fixpoint \
  && cabal update \
  && cabal install

FROM $BASE_IMAGE AS with-deps

COPY --from=fixpoint-builder /root/.local/bin/fixpoint /usr/bin/
RUN apt-get -qq update && apt-get install -qqy --no-install-recommends z3 \
  && /bin/rm -rf /var/lib/apt/lists/*

FROM with-deps AS flux-builder
COPY . /flux
WORKDIR /flux
RUN cargo xtask install

FROM flux-builder AS test

WORKDIR /flux
RUN cargo xtask test

# To have flux source available from inside the container, one can substitute `with-deps` with `flux-builder`,
# but if you want the changes to persist across containers (which is what's usually desired),
# then a bound volume with the flux project is a better solution 
FROM with-deps AS final
LABEL org.opencontainers.image.title="Flux - Liquid Types for Rust"
LABEL org.opencontainers.image.description="Docker image to build and test Flux"
LABEL org.opencontainers.image.vendor="ucsd-progsys"
LABEL org.opencontainers.image.source="https://github.com/flux-rs/flux"
LABEL org.opencontainers.image.licenses="MIT"

COPY --from=flux-builder \
  /usr/local/cargo/bin/rustc-flux \
  /usr/local/cargo/bin/cargo-flux \
  /usr/local/cargo/bin/
COPY --from=flux-builder /root/.flux /root/.flux