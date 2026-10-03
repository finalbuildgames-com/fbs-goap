#include <fbs/goap.h>
#include <stdio.h>
int main(void) {
    fbs_goap_config config = fbs_goap_config_default();
    fbs_goap_domain *context = NULL;
    if (fbs_goap_domain_create(&config, NULL, &context) != 0) return 1;
    printf("API version: %u\n", fbs_goap_version());
    fbs_goap_domain_destroy(context);
    return 0;
}
