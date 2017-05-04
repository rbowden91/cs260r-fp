#!/bin/sh
# runcoqide - run coqide and provide the right search path
# usage: ./runcoqide file.v
exec coqide -R VST/msl msl -R VST/veric veric -R VST/compcert compcert "$@"
