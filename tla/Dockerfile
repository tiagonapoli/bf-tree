# TLC model checker for the CPR snapshot TLA+ specs.
#
# Build:
#   docker build -f tla/Dockerfile -t bftree-tla tla
# Run:
#   docker run --rm bftree-tla

FROM eclipse-temurin:21-jre

ADD https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar /opt/tla2tools.jar

WORKDIR /work
COPY . .
RUN sed -i 's/\r$//' run.sh && chmod +x run.sh

ENTRYPOINT ["bash", "run.sh"]
