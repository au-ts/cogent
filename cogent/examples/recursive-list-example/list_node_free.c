static inline t5 list_alloc_node_0(unit_t x) {
    t2* node = malloc(sizeof(*node));
    t5 ret;

    if (!node) {
        ret.tag = TAG_ENUM_None;
        return ret;
    }

    ret.tag = TAG_ENUM_Some;
    ret.Some = node;
    return ret;
}

unit_t list_free_node_0(t2 * x) {
    free(x);

    unit_t z;
    return z;
}