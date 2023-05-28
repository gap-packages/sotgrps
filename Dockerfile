FROM gapsystem/gap-docker

MAINTAINER Eileen Pan <eileen.pan@monash.edu>

# Update version number each time after gap-docker container is updated
ENV GAP_VERSION 4.11.1

# Remove previous JupyterKernel installation, copy this repository and make new install

RUN cd /home/gap/inst/gap-${GAP_VERSION}/pkg/ \
    && wget https://github.com/gap-packages/sotgrps_gap_pkg/archive/master.zip \
    && unzip -q master.zip \
    && rm master.zip \
    && mv sotgrps_gap_pkg-master sotgrps_gap_pkg

USER gap

WORKDIR /home/gap/inst/gap-${GAP_VERSION}/pkg/sotgrps_gap_pkg/
