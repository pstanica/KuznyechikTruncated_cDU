#!/bin/bash

#==============================================================================
# SLURM DIRECTIVES (no changes here)
#==============================================================================
#SBATCH --job-name=kuznyechik_cDU
#SBATCH --output=kuznyechik_cDU_%j.out
#SBATCH --error=kuznyechik_cDU_%j.err
#SBATCH --time=48:00:00
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=64
#SBATCH --mem=128G

#==============================================================================
# ENVIRONMENT SETUP (no changes here)
#==============================================================================
echo "========================================================"
echo "Job Started: $(date)"
echo "Job ID: $SLURM_JOB_ID"
echo "Node: $SLURM_NODENAME"
echo "Cores: $SLURM_NTASKS"
echo "========================================================"

#==============================================================================
# EXECUTION (REPLACE THIS SECTION)
#==============================================================================
echo "Starting multi-round Kuznyechik analysis..."

# Define the rounds you want to test in a loop
for round_num in 9 8 7 6 5 4 3 2 1
do
    echo "--------------------------------------------------------"
    echo "Running analysis for $round_num rounds..."
    echo "--------------------------------------------------------"
    
    # Run the Python script, passing the current round number
    sage -python Multiproc_cDU_Enhanced_Kuznyechik_R9.py --rounds "$round_num"
    
    # Optional: Add a small delay between runs if needed
    sleep 3 
done

#==============================================================================
# CLEANUP (no changes here)
#==============================================================================
echo "========================================================"
echo "Job Finished: $(date)"
echo "========================================================"