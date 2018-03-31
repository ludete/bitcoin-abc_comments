//
// Created by Bitmain on 2018/3/19.
//
#define BEGIN_SERIALIZE_OBJECT()
  template <bool W, template <bool> class Archive>
  bool do_serialize(Archive<W> &ar) {
    ar.begin_object();
    bool r = do_serialize_object(ar);
    ar.end_object();
    return r;
  }

  template <bool W, template <bool> class Archive>
  bool do_serialize_object(Archive<W> &ar){


    if (!typename Archive<W>::is_saving())
    {
      set_hash_valid(false);
      set_blob_size_valid(false);
    }

    transaction_prefix * s = *static_cast<transaction_prefix *>(this)
    do {
    bool r = ::do_serialize(ar, s);
    if (!r || !ar.stream().good()) return false;
    } while(0);


    if (version == 1)
    {
      ar.tag("signatures");
      ar.begin_array();
      PREPARE_CUSTOM_VECTOR_SERIALIZATION(vin.size(), signatures);
      bool signatures_not_expected = signatures.empty();
      if (!signatures_not_expected && vin.size() != signatures.size())
        return false;

      for (size_t i = 0; i < vin.size(); ++i)
      {
        size_t signature_size = get_signature_size(vin[i]);
        if (signatures_not_expected)
        {
          if (0 == signature_size)
            continue;
          else
            return false;
        }

        PREPARE_CUSTOM_VECTOR_SERIALIZATION(signature_size, signatures[i]);
        if (signature_size != signatures[i].size())
          return false;

        FIELDS(signatures[i]);

        if (vin.size() - i > 1)
          ar.delimit_array();
      }
      ar.end_array();
    }

    return true;
  }

