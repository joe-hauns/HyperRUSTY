Dear TACAS Chair,

Thank you once again for coordinating the artifact evaluation for our submission HyperQB 2.0: A Bounded Model Checker for Hyperproperties. During the rebuttal period, we prepared an AMD64 Docker image to the best of our ability, and since all three reviewers are working on AMD64 machines, we kindly ask that they use this updated image for their evaluation and SmokeTests. (As noted, running the original ARM64 image through qemu introduces additional overhead and dependency-related errors, so we also suggest that Reviewer 3 switch to the new AMD64 image.)

We would also like to kindly ask the reviewers to pay particular attention to the section “Important Updates for TACAS Reviewers” in tacas_README.md. Our main goal is to provide a fully reproducible Docker image that enables reviewers to rerun all experiments from the paper as consistently as possible, and we hope that the AMD64 image helps streamline the evaluation across all setups.

We would be very grateful if the committee could invite the reviewers to rerun the SmokeTests with the updated image to ensure that no remaining technical issues affect the final evaluation.

Thank you very much for your time and support.